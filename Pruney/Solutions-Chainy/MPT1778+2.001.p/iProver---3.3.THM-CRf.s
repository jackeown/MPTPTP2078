%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:41 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 647 expanded)
%              Number of clauses        :  100 ( 164 expanded)
%              Number of leaves         :   14 ( 249 expanded)
%              Depth                    :   17
%              Number of atoms          : 1005 (10035 expanded)
%              Number of equality atoms :  246 ( 277 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   38 (   5 average)
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X3,X2)
                         => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f31,plain,(
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
     => ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,sK4),X3,X1)
          | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,sK4),u1_struct_0(X3),u1_struct_0(X1))
          | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,sK4)) )
        & m1_pre_topc(X3,X2)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(sK4,X2,X1)
        & v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
            ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
              | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,sK3,X4),sK3,X1)
              | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,sK3,X4),u1_struct_0(sK3),u1_struct_0(X1))
              | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,sK3,X4)) )
            & m1_pre_topc(sK3,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(X4,X2,X1)
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
                ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,sK2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X1,sK2,X3,X4),X3,X1)
                  | ~ v1_funct_2(k3_tmap_1(X0,X1,sK2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                  | ~ v1_funct_1(k3_tmap_1(X0,X1,sK2,X3,X4)) )
                & m1_pre_topc(X3,sK2)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                & v5_pre_topc(X4,sK2,X1)
                & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
                    ( ( ~ m1_subset_1(k3_tmap_1(X0,sK1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      | ~ v5_pre_topc(k3_tmap_1(X0,sK1,X2,X3,X4),X3,sK1)
                      | ~ v1_funct_2(k3_tmap_1(X0,sK1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1))
                      | ~ v1_funct_1(k3_tmap_1(X0,sK1,X2,X3,X4)) )
                    & m1_pre_topc(X3,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                    & v5_pre_topc(X4,X2,sK1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
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
                      ( ( ~ m1_subset_1(k3_tmap_1(sK0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK0,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(sK0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(sK0,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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

fof(f32,plain,
    ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) )
    & m1_pre_topc(sK3,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(sK4,sK2,sK1)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f26,f31,f30,f29,f28,f27])).

fof(f52,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(ennf_transformation,[],[f5])).

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
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(ennf_transformation,[],[f4])).

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
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_294,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_812,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_301,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_805,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_301])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_300,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_806,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_4,plain,
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
    inference(cnf_transformation,[],[f37])).

cnf(c_310,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X2_48,X0_48)
    | ~ m1_pre_topc(X2_48,X3_48)
    | ~ m1_pre_topc(X0_48,X3_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X3_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X3_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X3_48)
    | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_796,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X2_48,X3_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X3_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_303,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ m1_pre_topc(X2_48,X0_48)
    | m1_pre_topc(X2_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v2_pre_topc(X1_48) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_803,plain,
    ( m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X2_48,X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_1041,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X3_48) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_796,c_803])).

cnf(c_3111,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_1041])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_31,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_32,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_33,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_38,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_39,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3303,plain,
    ( v2_pre_topc(X1_48) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK4)
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3111,c_31,c_32,c_33,c_38,c_39])).

cnf(c_3304,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK4)
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3303])).

cnf(c_3315,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0_48,sK1,sK2,sK3,sK4)
    | m1_pre_topc(sK2,X0_48) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_3304])).

cnf(c_3,plain,
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
    inference(cnf_transformation,[],[f36])).

cnf(c_311,plain,
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
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_795,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_2305,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK4,X0_48)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_795])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_29,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_30,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_34,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_35,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_314,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v2_pre_topc(X1_48)
    | v2_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_792,plain,
    ( m1_pre_topc(X0_48,X1_48) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_1310,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_812,c_792])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_312,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1255,plain,
    ( ~ m1_pre_topc(sK2,X0_48)
    | ~ l1_pre_topc(X0_48)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_1360,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1255])).

cnf(c_1361,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1360])).

cnf(c_2782,plain,
    ( m1_pre_topc(X0_48,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK4,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2305,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_38,c_39,c_1310,c_1361])).

cnf(c_2783,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK4,X0_48)
    | m1_pre_topc(X0_48,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2782])).

cnf(c_2790,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_805,c_2783])).

cnf(c_3316,plain,
    ( k3_tmap_1(X0_48,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | m1_pre_topc(sK2,X0_48) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3315,c_2790])).

cnf(c_3701,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_812,c_3316])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_28,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3704,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3701,c_28,c_29,c_30])).

cnf(c_12,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_302,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_804,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_3707,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3704,c_804])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_309,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | m1_subset_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
    | ~ v1_funct_1(X0_49)
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1265,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK2,sK1,X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_49)
    | ~ l1_struct_0(X0_48)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_1867,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK2,sK1,X0_49,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_49)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_1868,plain,
    ( v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,X0_49,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1867])).

cnf(c_1870,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1868])).

cnf(c_1,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_313,plain,
    ( l1_struct_0(X0_48)
    | ~ l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1691,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_1692,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1691])).

cnf(c_794,plain,
    ( m1_pre_topc(X0_48,X1_48) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_1586,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_794])).

cnf(c_1280,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_1281,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1280])).

cnf(c_8,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(k2_tmap_1(X1,X2,X0,X3),X3,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_306,plain,
    ( ~ v5_pre_topc(X0_49,X0_48,X1_48)
    | v5_pre_topc(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),X2_48,X1_48)
    | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X2_48,X0_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X2_48)
    | v2_struct_0(X0_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X0_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1215,plain,
    ( ~ v5_pre_topc(X0_49,sK2,X0_48)
    | v5_pre_topc(k2_tmap_1(sK2,X0_48,X0_49,sK3),sK3,X0_48)
    | ~ v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(X0_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_48))))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(X0_48)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X0_48)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_48)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_1216,plain,
    ( v5_pre_topc(X0_49,sK2,X0_48) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_48,X0_49,sK3),sK3,X0_48) = iProver_top
    | v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(X0_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_48)))) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1215])).

cnf(c_1218,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) = iProver_top
    | v5_pre_topc(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1216])).

cnf(c_9,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_305,plain,
    ( ~ v5_pre_topc(X0_49,X0_48,X1_48)
    | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | v1_funct_2(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),u1_struct_0(X2_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X2_48,X0_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X2_48)
    | v2_struct_0(X0_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X0_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1200,plain,
    ( ~ v5_pre_topc(X0_49,sK2,X0_48)
    | ~ v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(X0_48))
    | v1_funct_2(k2_tmap_1(sK2,X0_48,X0_49,sK3),u1_struct_0(sK3),u1_struct_0(X0_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_48))))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(X0_48)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X0_48)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_48)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_1201,plain,
    ( v5_pre_topc(X0_49,sK2,X0_48) != iProver_top
    | v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(X0_48)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_48,X0_49,sK3),u1_struct_0(sK3),u1_struct_0(X0_48)) = iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_48)))) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1200])).

cnf(c_1203,plain,
    ( v5_pre_topc(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1201])).

cnf(c_10,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_304,plain,
    ( ~ v5_pre_topc(X0_49,X0_48,X1_48)
    | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X2_48,X0_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X2_48)
    | v2_struct_0(X0_48)
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48))
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X0_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1170,plain,
    ( ~ v5_pre_topc(X0_49,sK2,X0_48)
    | ~ v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(X0_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_48))))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(X0_48)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_tmap_1(sK2,X0_48,X0_49,sK3))
    | ~ l1_pre_topc(X0_48)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_48)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_1171,plain,
    ( v5_pre_topc(X0_49,sK2,X0_48) != iProver_top
    | v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(X0_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_48)))) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_48,X0_49,sK3)) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1170])).

cnf(c_1173,plain,
    ( v5_pre_topc(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_70,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_72,plain,
    ( l1_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_42,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_40,plain,
    ( v5_pre_topc(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_36,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3707,c_1870,c_1692,c_1586,c_1361,c_1310,c_1281,c_1218,c_1203,c_1173,c_72,c_42,c_41,c_40,c_39,c_38,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 11:49:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.48/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.03  
% 2.48/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.48/1.03  
% 2.48/1.03  ------  iProver source info
% 2.48/1.03  
% 2.48/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.48/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.48/1.03  git: non_committed_changes: false
% 2.48/1.03  git: last_make_outside_of_git: false
% 2.48/1.03  
% 2.48/1.03  ------ 
% 2.48/1.03  
% 2.48/1.03  ------ Input Options
% 2.48/1.03  
% 2.48/1.03  --out_options                           all
% 2.48/1.03  --tptp_safe_out                         true
% 2.48/1.03  --problem_path                          ""
% 2.48/1.03  --include_path                          ""
% 2.48/1.03  --clausifier                            res/vclausify_rel
% 2.48/1.03  --clausifier_options                    --mode clausify
% 2.48/1.03  --stdin                                 false
% 2.48/1.03  --stats_out                             all
% 2.48/1.03  
% 2.48/1.03  ------ General Options
% 2.48/1.03  
% 2.48/1.03  --fof                                   false
% 2.48/1.03  --time_out_real                         305.
% 2.48/1.03  --time_out_virtual                      -1.
% 2.48/1.03  --symbol_type_check                     false
% 2.48/1.03  --clausify_out                          false
% 2.48/1.03  --sig_cnt_out                           false
% 2.48/1.03  --trig_cnt_out                          false
% 2.48/1.03  --trig_cnt_out_tolerance                1.
% 2.48/1.03  --trig_cnt_out_sk_spl                   false
% 2.48/1.03  --abstr_cl_out                          false
% 2.48/1.03  
% 2.48/1.03  ------ Global Options
% 2.48/1.03  
% 2.48/1.03  --schedule                              default
% 2.48/1.03  --add_important_lit                     false
% 2.48/1.03  --prop_solver_per_cl                    1000
% 2.48/1.03  --min_unsat_core                        false
% 2.48/1.03  --soft_assumptions                      false
% 2.48/1.03  --soft_lemma_size                       3
% 2.48/1.03  --prop_impl_unit_size                   0
% 2.48/1.03  --prop_impl_unit                        []
% 2.48/1.03  --share_sel_clauses                     true
% 2.48/1.03  --reset_solvers                         false
% 2.48/1.03  --bc_imp_inh                            [conj_cone]
% 2.48/1.03  --conj_cone_tolerance                   3.
% 2.48/1.03  --extra_neg_conj                        none
% 2.48/1.03  --large_theory_mode                     true
% 2.48/1.03  --prolific_symb_bound                   200
% 2.48/1.03  --lt_threshold                          2000
% 2.48/1.03  --clause_weak_htbl                      true
% 2.48/1.03  --gc_record_bc_elim                     false
% 2.48/1.03  
% 2.48/1.03  ------ Preprocessing Options
% 2.48/1.03  
% 2.48/1.03  --preprocessing_flag                    true
% 2.48/1.03  --time_out_prep_mult                    0.1
% 2.48/1.03  --splitting_mode                        input
% 2.48/1.03  --splitting_grd                         true
% 2.48/1.03  --splitting_cvd                         false
% 2.48/1.03  --splitting_cvd_svl                     false
% 2.48/1.03  --splitting_nvd                         32
% 2.48/1.03  --sub_typing                            true
% 2.48/1.03  --prep_gs_sim                           true
% 2.48/1.03  --prep_unflatten                        true
% 2.48/1.03  --prep_res_sim                          true
% 2.48/1.03  --prep_upred                            true
% 2.48/1.03  --prep_sem_filter                       exhaustive
% 2.48/1.03  --prep_sem_filter_out                   false
% 2.48/1.03  --pred_elim                             true
% 2.48/1.03  --res_sim_input                         true
% 2.48/1.03  --eq_ax_congr_red                       true
% 2.48/1.03  --pure_diseq_elim                       true
% 2.48/1.03  --brand_transform                       false
% 2.48/1.03  --non_eq_to_eq                          false
% 2.48/1.03  --prep_def_merge                        true
% 2.48/1.03  --prep_def_merge_prop_impl              false
% 2.48/1.03  --prep_def_merge_mbd                    true
% 2.48/1.03  --prep_def_merge_tr_red                 false
% 2.48/1.03  --prep_def_merge_tr_cl                  false
% 2.48/1.03  --smt_preprocessing                     true
% 2.48/1.03  --smt_ac_axioms                         fast
% 2.48/1.03  --preprocessed_out                      false
% 2.48/1.03  --preprocessed_stats                    false
% 2.48/1.03  
% 2.48/1.03  ------ Abstraction refinement Options
% 2.48/1.03  
% 2.48/1.03  --abstr_ref                             []
% 2.48/1.03  --abstr_ref_prep                        false
% 2.48/1.03  --abstr_ref_until_sat                   false
% 2.48/1.03  --abstr_ref_sig_restrict                funpre
% 2.48/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/1.03  --abstr_ref_under                       []
% 2.48/1.03  
% 2.48/1.03  ------ SAT Options
% 2.48/1.03  
% 2.48/1.03  --sat_mode                              false
% 2.48/1.03  --sat_fm_restart_options                ""
% 2.48/1.03  --sat_gr_def                            false
% 2.48/1.03  --sat_epr_types                         true
% 2.48/1.03  --sat_non_cyclic_types                  false
% 2.48/1.03  --sat_finite_models                     false
% 2.48/1.03  --sat_fm_lemmas                         false
% 2.48/1.03  --sat_fm_prep                           false
% 2.48/1.03  --sat_fm_uc_incr                        true
% 2.48/1.03  --sat_out_model                         small
% 2.48/1.03  --sat_out_clauses                       false
% 2.48/1.03  
% 2.48/1.03  ------ QBF Options
% 2.48/1.03  
% 2.48/1.03  --qbf_mode                              false
% 2.48/1.03  --qbf_elim_univ                         false
% 2.48/1.03  --qbf_dom_inst                          none
% 2.48/1.03  --qbf_dom_pre_inst                      false
% 2.48/1.03  --qbf_sk_in                             false
% 2.48/1.03  --qbf_pred_elim                         true
% 2.48/1.03  --qbf_split                             512
% 2.48/1.03  
% 2.48/1.03  ------ BMC1 Options
% 2.48/1.03  
% 2.48/1.03  --bmc1_incremental                      false
% 2.48/1.03  --bmc1_axioms                           reachable_all
% 2.48/1.03  --bmc1_min_bound                        0
% 2.48/1.03  --bmc1_max_bound                        -1
% 2.48/1.03  --bmc1_max_bound_default                -1
% 2.48/1.03  --bmc1_symbol_reachability              true
% 2.48/1.03  --bmc1_property_lemmas                  false
% 2.48/1.03  --bmc1_k_induction                      false
% 2.48/1.03  --bmc1_non_equiv_states                 false
% 2.48/1.03  --bmc1_deadlock                         false
% 2.48/1.03  --bmc1_ucm                              false
% 2.48/1.03  --bmc1_add_unsat_core                   none
% 2.48/1.03  --bmc1_unsat_core_children              false
% 2.48/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/1.03  --bmc1_out_stat                         full
% 2.48/1.03  --bmc1_ground_init                      false
% 2.48/1.03  --bmc1_pre_inst_next_state              false
% 2.48/1.03  --bmc1_pre_inst_state                   false
% 2.48/1.03  --bmc1_pre_inst_reach_state             false
% 2.48/1.03  --bmc1_out_unsat_core                   false
% 2.48/1.03  --bmc1_aig_witness_out                  false
% 2.48/1.03  --bmc1_verbose                          false
% 2.48/1.03  --bmc1_dump_clauses_tptp                false
% 2.48/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.48/1.03  --bmc1_dump_file                        -
% 2.48/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.48/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.48/1.03  --bmc1_ucm_extend_mode                  1
% 2.48/1.03  --bmc1_ucm_init_mode                    2
% 2.48/1.03  --bmc1_ucm_cone_mode                    none
% 2.48/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.48/1.03  --bmc1_ucm_relax_model                  4
% 2.48/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.48/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/1.03  --bmc1_ucm_layered_model                none
% 2.48/1.03  --bmc1_ucm_max_lemma_size               10
% 2.48/1.03  
% 2.48/1.03  ------ AIG Options
% 2.48/1.03  
% 2.48/1.03  --aig_mode                              false
% 2.48/1.03  
% 2.48/1.03  ------ Instantiation Options
% 2.48/1.03  
% 2.48/1.03  --instantiation_flag                    true
% 2.48/1.03  --inst_sos_flag                         false
% 2.48/1.03  --inst_sos_phase                        true
% 2.48/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/1.03  --inst_lit_sel_side                     num_symb
% 2.48/1.03  --inst_solver_per_active                1400
% 2.48/1.03  --inst_solver_calls_frac                1.
% 2.48/1.03  --inst_passive_queue_type               priority_queues
% 2.48/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/1.03  --inst_passive_queues_freq              [25;2]
% 2.48/1.03  --inst_dismatching                      true
% 2.48/1.03  --inst_eager_unprocessed_to_passive     true
% 2.48/1.03  --inst_prop_sim_given                   true
% 2.48/1.03  --inst_prop_sim_new                     false
% 2.48/1.03  --inst_subs_new                         false
% 2.48/1.03  --inst_eq_res_simp                      false
% 2.48/1.03  --inst_subs_given                       false
% 2.48/1.03  --inst_orphan_elimination               true
% 2.48/1.03  --inst_learning_loop_flag               true
% 2.48/1.03  --inst_learning_start                   3000
% 2.48/1.03  --inst_learning_factor                  2
% 2.48/1.03  --inst_start_prop_sim_after_learn       3
% 2.48/1.03  --inst_sel_renew                        solver
% 2.48/1.03  --inst_lit_activity_flag                true
% 2.48/1.03  --inst_restr_to_given                   false
% 2.48/1.03  --inst_activity_threshold               500
% 2.48/1.03  --inst_out_proof                        true
% 2.48/1.03  
% 2.48/1.03  ------ Resolution Options
% 2.48/1.03  
% 2.48/1.03  --resolution_flag                       true
% 2.48/1.03  --res_lit_sel                           adaptive
% 2.48/1.03  --res_lit_sel_side                      none
% 2.48/1.03  --res_ordering                          kbo
% 2.48/1.03  --res_to_prop_solver                    active
% 2.48/1.03  --res_prop_simpl_new                    false
% 2.48/1.03  --res_prop_simpl_given                  true
% 2.48/1.03  --res_passive_queue_type                priority_queues
% 2.48/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/1.03  --res_passive_queues_freq               [15;5]
% 2.48/1.03  --res_forward_subs                      full
% 2.48/1.03  --res_backward_subs                     full
% 2.48/1.03  --res_forward_subs_resolution           true
% 2.48/1.03  --res_backward_subs_resolution          true
% 2.48/1.03  --res_orphan_elimination                true
% 2.48/1.03  --res_time_limit                        2.
% 2.48/1.03  --res_out_proof                         true
% 2.48/1.03  
% 2.48/1.03  ------ Superposition Options
% 2.48/1.03  
% 2.48/1.03  --superposition_flag                    true
% 2.48/1.03  --sup_passive_queue_type                priority_queues
% 2.48/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.48/1.03  --demod_completeness_check              fast
% 2.48/1.03  --demod_use_ground                      true
% 2.48/1.03  --sup_to_prop_solver                    passive
% 2.48/1.03  --sup_prop_simpl_new                    true
% 2.48/1.03  --sup_prop_simpl_given                  true
% 2.48/1.03  --sup_fun_splitting                     false
% 2.48/1.03  --sup_smt_interval                      50000
% 2.48/1.03  
% 2.48/1.03  ------ Superposition Simplification Setup
% 2.48/1.03  
% 2.48/1.03  --sup_indices_passive                   []
% 2.48/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.03  --sup_full_bw                           [BwDemod]
% 2.48/1.03  --sup_immed_triv                        [TrivRules]
% 2.48/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.03  --sup_immed_bw_main                     []
% 2.48/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.03  
% 2.48/1.03  ------ Combination Options
% 2.48/1.03  
% 2.48/1.03  --comb_res_mult                         3
% 2.48/1.03  --comb_sup_mult                         2
% 2.48/1.03  --comb_inst_mult                        10
% 2.48/1.03  
% 2.48/1.03  ------ Debug Options
% 2.48/1.03  
% 2.48/1.03  --dbg_backtrace                         false
% 2.48/1.03  --dbg_dump_prop_clauses                 false
% 2.48/1.03  --dbg_dump_prop_clauses_file            -
% 2.48/1.03  --dbg_out_stat                          false
% 2.48/1.03  ------ Parsing...
% 2.48/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.48/1.03  
% 2.48/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.48/1.03  
% 2.48/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.48/1.03  
% 2.48/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.48/1.03  ------ Proving...
% 2.48/1.03  ------ Problem Properties 
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  clauses                                 28
% 2.48/1.03  conjectures                             16
% 2.48/1.03  EPR                                     17
% 2.48/1.03  Horn                                    23
% 2.48/1.03  unary                                   15
% 2.48/1.03  binary                                  1
% 2.48/1.03  lits                                    117
% 2.48/1.03  lits eq                                 2
% 2.48/1.03  fd_pure                                 0
% 2.48/1.03  fd_pseudo                               0
% 2.48/1.03  fd_cond                                 0
% 2.48/1.03  fd_pseudo_cond                          0
% 2.48/1.03  AC symbols                              0
% 2.48/1.03  
% 2.48/1.03  ------ Schedule dynamic 5 is on 
% 2.48/1.03  
% 2.48/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  ------ 
% 2.48/1.03  Current options:
% 2.48/1.03  ------ 
% 2.48/1.03  
% 2.48/1.03  ------ Input Options
% 2.48/1.03  
% 2.48/1.03  --out_options                           all
% 2.48/1.03  --tptp_safe_out                         true
% 2.48/1.03  --problem_path                          ""
% 2.48/1.03  --include_path                          ""
% 2.48/1.03  --clausifier                            res/vclausify_rel
% 2.48/1.03  --clausifier_options                    --mode clausify
% 2.48/1.03  --stdin                                 false
% 2.48/1.03  --stats_out                             all
% 2.48/1.03  
% 2.48/1.03  ------ General Options
% 2.48/1.03  
% 2.48/1.03  --fof                                   false
% 2.48/1.03  --time_out_real                         305.
% 2.48/1.03  --time_out_virtual                      -1.
% 2.48/1.03  --symbol_type_check                     false
% 2.48/1.03  --clausify_out                          false
% 2.48/1.03  --sig_cnt_out                           false
% 2.48/1.03  --trig_cnt_out                          false
% 2.48/1.03  --trig_cnt_out_tolerance                1.
% 2.48/1.03  --trig_cnt_out_sk_spl                   false
% 2.48/1.03  --abstr_cl_out                          false
% 2.48/1.03  
% 2.48/1.03  ------ Global Options
% 2.48/1.03  
% 2.48/1.03  --schedule                              default
% 2.48/1.03  --add_important_lit                     false
% 2.48/1.03  --prop_solver_per_cl                    1000
% 2.48/1.03  --min_unsat_core                        false
% 2.48/1.03  --soft_assumptions                      false
% 2.48/1.03  --soft_lemma_size                       3
% 2.48/1.03  --prop_impl_unit_size                   0
% 2.48/1.03  --prop_impl_unit                        []
% 2.48/1.03  --share_sel_clauses                     true
% 2.48/1.03  --reset_solvers                         false
% 2.48/1.03  --bc_imp_inh                            [conj_cone]
% 2.48/1.03  --conj_cone_tolerance                   3.
% 2.48/1.03  --extra_neg_conj                        none
% 2.48/1.03  --large_theory_mode                     true
% 2.48/1.03  --prolific_symb_bound                   200
% 2.48/1.03  --lt_threshold                          2000
% 2.48/1.03  --clause_weak_htbl                      true
% 2.48/1.03  --gc_record_bc_elim                     false
% 2.48/1.03  
% 2.48/1.03  ------ Preprocessing Options
% 2.48/1.03  
% 2.48/1.03  --preprocessing_flag                    true
% 2.48/1.03  --time_out_prep_mult                    0.1
% 2.48/1.03  --splitting_mode                        input
% 2.48/1.03  --splitting_grd                         true
% 2.48/1.03  --splitting_cvd                         false
% 2.48/1.03  --splitting_cvd_svl                     false
% 2.48/1.03  --splitting_nvd                         32
% 2.48/1.03  --sub_typing                            true
% 2.48/1.03  --prep_gs_sim                           true
% 2.48/1.03  --prep_unflatten                        true
% 2.48/1.03  --prep_res_sim                          true
% 2.48/1.03  --prep_upred                            true
% 2.48/1.03  --prep_sem_filter                       exhaustive
% 2.48/1.03  --prep_sem_filter_out                   false
% 2.48/1.03  --pred_elim                             true
% 2.48/1.03  --res_sim_input                         true
% 2.48/1.03  --eq_ax_congr_red                       true
% 2.48/1.03  --pure_diseq_elim                       true
% 2.48/1.03  --brand_transform                       false
% 2.48/1.03  --non_eq_to_eq                          false
% 2.48/1.03  --prep_def_merge                        true
% 2.48/1.03  --prep_def_merge_prop_impl              false
% 2.48/1.03  --prep_def_merge_mbd                    true
% 2.48/1.03  --prep_def_merge_tr_red                 false
% 2.48/1.03  --prep_def_merge_tr_cl                  false
% 2.48/1.03  --smt_preprocessing                     true
% 2.48/1.03  --smt_ac_axioms                         fast
% 2.48/1.03  --preprocessed_out                      false
% 2.48/1.03  --preprocessed_stats                    false
% 2.48/1.03  
% 2.48/1.03  ------ Abstraction refinement Options
% 2.48/1.03  
% 2.48/1.03  --abstr_ref                             []
% 2.48/1.03  --abstr_ref_prep                        false
% 2.48/1.03  --abstr_ref_until_sat                   false
% 2.48/1.03  --abstr_ref_sig_restrict                funpre
% 2.48/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/1.03  --abstr_ref_under                       []
% 2.48/1.03  
% 2.48/1.03  ------ SAT Options
% 2.48/1.03  
% 2.48/1.03  --sat_mode                              false
% 2.48/1.03  --sat_fm_restart_options                ""
% 2.48/1.03  --sat_gr_def                            false
% 2.48/1.03  --sat_epr_types                         true
% 2.48/1.03  --sat_non_cyclic_types                  false
% 2.48/1.03  --sat_finite_models                     false
% 2.48/1.03  --sat_fm_lemmas                         false
% 2.48/1.03  --sat_fm_prep                           false
% 2.48/1.03  --sat_fm_uc_incr                        true
% 2.48/1.03  --sat_out_model                         small
% 2.48/1.03  --sat_out_clauses                       false
% 2.48/1.03  
% 2.48/1.03  ------ QBF Options
% 2.48/1.03  
% 2.48/1.03  --qbf_mode                              false
% 2.48/1.03  --qbf_elim_univ                         false
% 2.48/1.03  --qbf_dom_inst                          none
% 2.48/1.03  --qbf_dom_pre_inst                      false
% 2.48/1.03  --qbf_sk_in                             false
% 2.48/1.03  --qbf_pred_elim                         true
% 2.48/1.03  --qbf_split                             512
% 2.48/1.03  
% 2.48/1.03  ------ BMC1 Options
% 2.48/1.03  
% 2.48/1.03  --bmc1_incremental                      false
% 2.48/1.03  --bmc1_axioms                           reachable_all
% 2.48/1.03  --bmc1_min_bound                        0
% 2.48/1.03  --bmc1_max_bound                        -1
% 2.48/1.03  --bmc1_max_bound_default                -1
% 2.48/1.03  --bmc1_symbol_reachability              true
% 2.48/1.03  --bmc1_property_lemmas                  false
% 2.48/1.03  --bmc1_k_induction                      false
% 2.48/1.03  --bmc1_non_equiv_states                 false
% 2.48/1.03  --bmc1_deadlock                         false
% 2.48/1.03  --bmc1_ucm                              false
% 2.48/1.03  --bmc1_add_unsat_core                   none
% 2.48/1.03  --bmc1_unsat_core_children              false
% 2.48/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/1.03  --bmc1_out_stat                         full
% 2.48/1.03  --bmc1_ground_init                      false
% 2.48/1.03  --bmc1_pre_inst_next_state              false
% 2.48/1.03  --bmc1_pre_inst_state                   false
% 2.48/1.03  --bmc1_pre_inst_reach_state             false
% 2.48/1.03  --bmc1_out_unsat_core                   false
% 2.48/1.03  --bmc1_aig_witness_out                  false
% 2.48/1.03  --bmc1_verbose                          false
% 2.48/1.03  --bmc1_dump_clauses_tptp                false
% 2.48/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.48/1.03  --bmc1_dump_file                        -
% 2.48/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.48/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.48/1.03  --bmc1_ucm_extend_mode                  1
% 2.48/1.03  --bmc1_ucm_init_mode                    2
% 2.48/1.03  --bmc1_ucm_cone_mode                    none
% 2.48/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.48/1.03  --bmc1_ucm_relax_model                  4
% 2.48/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.48/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/1.03  --bmc1_ucm_layered_model                none
% 2.48/1.03  --bmc1_ucm_max_lemma_size               10
% 2.48/1.03  
% 2.48/1.03  ------ AIG Options
% 2.48/1.03  
% 2.48/1.03  --aig_mode                              false
% 2.48/1.03  
% 2.48/1.03  ------ Instantiation Options
% 2.48/1.03  
% 2.48/1.03  --instantiation_flag                    true
% 2.48/1.03  --inst_sos_flag                         false
% 2.48/1.03  --inst_sos_phase                        true
% 2.48/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/1.03  --inst_lit_sel_side                     none
% 2.48/1.03  --inst_solver_per_active                1400
% 2.48/1.03  --inst_solver_calls_frac                1.
% 2.48/1.03  --inst_passive_queue_type               priority_queues
% 2.48/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/1.03  --inst_passive_queues_freq              [25;2]
% 2.48/1.03  --inst_dismatching                      true
% 2.48/1.03  --inst_eager_unprocessed_to_passive     true
% 2.48/1.03  --inst_prop_sim_given                   true
% 2.48/1.03  --inst_prop_sim_new                     false
% 2.48/1.03  --inst_subs_new                         false
% 2.48/1.03  --inst_eq_res_simp                      false
% 2.48/1.03  --inst_subs_given                       false
% 2.48/1.03  --inst_orphan_elimination               true
% 2.48/1.03  --inst_learning_loop_flag               true
% 2.48/1.03  --inst_learning_start                   3000
% 2.48/1.03  --inst_learning_factor                  2
% 2.48/1.03  --inst_start_prop_sim_after_learn       3
% 2.48/1.03  --inst_sel_renew                        solver
% 2.48/1.03  --inst_lit_activity_flag                true
% 2.48/1.03  --inst_restr_to_given                   false
% 2.48/1.03  --inst_activity_threshold               500
% 2.48/1.03  --inst_out_proof                        true
% 2.48/1.03  
% 2.48/1.03  ------ Resolution Options
% 2.48/1.03  
% 2.48/1.03  --resolution_flag                       false
% 2.48/1.03  --res_lit_sel                           adaptive
% 2.48/1.03  --res_lit_sel_side                      none
% 2.48/1.03  --res_ordering                          kbo
% 2.48/1.03  --res_to_prop_solver                    active
% 2.48/1.03  --res_prop_simpl_new                    false
% 2.48/1.03  --res_prop_simpl_given                  true
% 2.48/1.03  --res_passive_queue_type                priority_queues
% 2.48/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/1.03  --res_passive_queues_freq               [15;5]
% 2.48/1.03  --res_forward_subs                      full
% 2.48/1.03  --res_backward_subs                     full
% 2.48/1.03  --res_forward_subs_resolution           true
% 2.48/1.03  --res_backward_subs_resolution          true
% 2.48/1.03  --res_orphan_elimination                true
% 2.48/1.03  --res_time_limit                        2.
% 2.48/1.03  --res_out_proof                         true
% 2.48/1.03  
% 2.48/1.03  ------ Superposition Options
% 2.48/1.03  
% 2.48/1.03  --superposition_flag                    true
% 2.48/1.03  --sup_passive_queue_type                priority_queues
% 2.48/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.48/1.03  --demod_completeness_check              fast
% 2.48/1.03  --demod_use_ground                      true
% 2.48/1.03  --sup_to_prop_solver                    passive
% 2.48/1.03  --sup_prop_simpl_new                    true
% 2.48/1.03  --sup_prop_simpl_given                  true
% 2.48/1.03  --sup_fun_splitting                     false
% 2.48/1.03  --sup_smt_interval                      50000
% 2.48/1.03  
% 2.48/1.03  ------ Superposition Simplification Setup
% 2.48/1.03  
% 2.48/1.03  --sup_indices_passive                   []
% 2.48/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.03  --sup_full_bw                           [BwDemod]
% 2.48/1.03  --sup_immed_triv                        [TrivRules]
% 2.48/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.03  --sup_immed_bw_main                     []
% 2.48/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.03  
% 2.48/1.03  ------ Combination Options
% 2.48/1.03  
% 2.48/1.03  --comb_res_mult                         3
% 2.48/1.03  --comb_sup_mult                         2
% 2.48/1.03  --comb_inst_mult                        10
% 2.48/1.03  
% 2.48/1.03  ------ Debug Options
% 2.48/1.03  
% 2.48/1.03  --dbg_backtrace                         false
% 2.48/1.03  --dbg_dump_prop_clauses                 false
% 2.48/1.03  --dbg_dump_prop_clauses_file            -
% 2.48/1.03  --dbg_out_stat                          false
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  ------ Proving...
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  % SZS status Theorem for theBenchmark.p
% 2.48/1.03  
% 2.48/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.48/1.03  
% 2.48/1.03  fof(f9,conjecture,(
% 2.48/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)))))))))),
% 2.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f10,negated_conjecture,(
% 2.48/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)))))))))),
% 2.48/1.03    inference(negated_conjecture,[],[f9])).
% 2.48/1.03  
% 2.48/1.03  fof(f25,plain,(
% 2.48/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.48/1.03    inference(ennf_transformation,[],[f10])).
% 2.48/1.03  
% 2.48/1.03  fof(f26,plain,(
% 2.48/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.48/1.03    inference(flattening,[],[f25])).
% 2.48/1.03  
% 2.48/1.03  fof(f31,plain,(
% 2.48/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,sK4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,sK4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,sK4))) & m1_pre_topc(X3,X2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(sK4,X2,X1) & v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.48/1.03    introduced(choice_axiom,[])).
% 2.48/1.03  
% 2.48/1.03  fof(f30,plain,(
% 2.48/1.03    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,sK3,X4),sK3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,sK3,X4),u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,sK3,X4))) & m1_pre_topc(sK3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.48/1.03    introduced(choice_axiom,[])).
% 2.48/1.03  
% 2.48/1.03  fof(f29,plain,(
% 2.48/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,sK2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,sK2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,sK2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,sK2,X3,X4))) & m1_pre_topc(X3,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X4,sK2,X1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.48/1.03    introduced(choice_axiom,[])).
% 2.48/1.03  
% 2.48/1.03  fof(f28,plain,(
% 2.48/1.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,sK1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(X0,sK1,X2,X3,X4),X3,sK1) | ~v1_funct_2(k3_tmap_1(X0,sK1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(X0,sK1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(X4,X2,sK1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.48/1.03    introduced(choice_axiom,[])).
% 2.48/1.03  
% 2.48/1.03  fof(f27,plain,(
% 2.48/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.48/1.03    introduced(choice_axiom,[])).
% 2.48/1.03  
% 2.48/1.03  fof(f32,plain,(
% 2.48/1.03    (((((~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) & m1_pre_topc(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(sK4,sK2,sK1) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.48/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f26,f31,f30,f29,f28,f27])).
% 2.48/1.03  
% 2.48/1.03  fof(f52,plain,(
% 2.48/1.03    m1_pre_topc(sK2,sK0)),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  fof(f59,plain,(
% 2.48/1.03    m1_pre_topc(sK3,sK2)),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  fof(f58,plain,(
% 2.48/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  fof(f5,axiom,(
% 2.48/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f17,plain,(
% 2.48/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/1.03    inference(ennf_transformation,[],[f5])).
% 2.48/1.03  
% 2.48/1.03  fof(f18,plain,(
% 2.48/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/1.03    inference(flattening,[],[f17])).
% 2.48/1.03  
% 2.48/1.03  fof(f37,plain,(
% 2.48/1.03    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.03    inference(cnf_transformation,[],[f18])).
% 2.48/1.03  
% 2.48/1.03  fof(f8,axiom,(
% 2.48/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f23,plain,(
% 2.48/1.03    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.48/1.03    inference(ennf_transformation,[],[f8])).
% 2.48/1.03  
% 2.48/1.03  fof(f24,plain,(
% 2.48/1.03    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.48/1.03    inference(flattening,[],[f23])).
% 2.48/1.03  
% 2.48/1.03  fof(f44,plain,(
% 2.48/1.03    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.48/1.03    inference(cnf_transformation,[],[f24])).
% 2.48/1.03  
% 2.48/1.03  fof(f48,plain,(
% 2.48/1.03    ~v2_struct_0(sK1)),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  fof(f49,plain,(
% 2.48/1.03    v2_pre_topc(sK1)),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  fof(f50,plain,(
% 2.48/1.03    l1_pre_topc(sK1)),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  fof(f55,plain,(
% 2.48/1.03    v1_funct_1(sK4)),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  fof(f56,plain,(
% 2.48/1.03    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  fof(f4,axiom,(
% 2.48/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f15,plain,(
% 2.48/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/1.03    inference(ennf_transformation,[],[f4])).
% 2.48/1.03  
% 2.48/1.03  fof(f16,plain,(
% 2.48/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/1.03    inference(flattening,[],[f15])).
% 2.48/1.03  
% 2.48/1.03  fof(f36,plain,(
% 2.48/1.03    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.03    inference(cnf_transformation,[],[f16])).
% 2.48/1.03  
% 2.48/1.03  fof(f46,plain,(
% 2.48/1.03    v2_pre_topc(sK0)),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  fof(f47,plain,(
% 2.48/1.03    l1_pre_topc(sK0)),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  fof(f51,plain,(
% 2.48/1.03    ~v2_struct_0(sK2)),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  fof(f1,axiom,(
% 2.48/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f11,plain,(
% 2.48/1.03    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.48/1.03    inference(ennf_transformation,[],[f1])).
% 2.48/1.03  
% 2.48/1.03  fof(f12,plain,(
% 2.48/1.03    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.48/1.03    inference(flattening,[],[f11])).
% 2.48/1.03  
% 2.48/1.03  fof(f33,plain,(
% 2.48/1.03    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.48/1.03    inference(cnf_transformation,[],[f12])).
% 2.48/1.03  
% 2.48/1.03  fof(f3,axiom,(
% 2.48/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f14,plain,(
% 2.48/1.03    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.48/1.03    inference(ennf_transformation,[],[f3])).
% 2.48/1.03  
% 2.48/1.03  fof(f35,plain,(
% 2.48/1.03    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.48/1.03    inference(cnf_transformation,[],[f14])).
% 2.48/1.03  
% 2.48/1.03  fof(f45,plain,(
% 2.48/1.03    ~v2_struct_0(sK0)),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  fof(f60,plain,(
% 2.48/1.03    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  fof(f6,axiom,(
% 2.48/1.03    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f19,plain,(
% 2.48/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.48/1.03    inference(ennf_transformation,[],[f6])).
% 2.48/1.03  
% 2.48/1.03  fof(f20,plain,(
% 2.48/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.48/1.03    inference(flattening,[],[f19])).
% 2.48/1.03  
% 2.48/1.03  fof(f40,plain,(
% 2.48/1.03    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.48/1.03    inference(cnf_transformation,[],[f20])).
% 2.48/1.03  
% 2.48/1.03  fof(f2,axiom,(
% 2.48/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f13,plain,(
% 2.48/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.48/1.03    inference(ennf_transformation,[],[f2])).
% 2.48/1.03  
% 2.48/1.03  fof(f34,plain,(
% 2.48/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.48/1.03    inference(cnf_transformation,[],[f13])).
% 2.48/1.03  
% 2.48/1.03  fof(f7,axiom,(
% 2.48/1.03    ! [X0,X1,X2,X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f21,plain,(
% 2.48/1.03    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/1.03    inference(ennf_transformation,[],[f7])).
% 2.48/1.03  
% 2.48/1.03  fof(f22,plain,(
% 2.48/1.03    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/1.03    inference(flattening,[],[f21])).
% 2.48/1.03  
% 2.48/1.03  fof(f43,plain,(
% 2.48/1.03    ( ! [X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.03    inference(cnf_transformation,[],[f22])).
% 2.48/1.03  
% 2.48/1.03  fof(f42,plain,(
% 2.48/1.03    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.03    inference(cnf_transformation,[],[f22])).
% 2.48/1.03  
% 2.48/1.03  fof(f41,plain,(
% 2.48/1.03    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.03    inference(cnf_transformation,[],[f22])).
% 2.48/1.03  
% 2.48/1.03  fof(f57,plain,(
% 2.48/1.03    v5_pre_topc(sK4,sK2,sK1)),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  fof(f53,plain,(
% 2.48/1.03    ~v2_struct_0(sK3)),
% 2.48/1.03    inference(cnf_transformation,[],[f32])).
% 2.48/1.03  
% 2.48/1.03  cnf(c_20,negated_conjecture,
% 2.48/1.03      ( m1_pre_topc(sK2,sK0) ),
% 2.48/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_294,negated_conjecture,
% 2.48/1.03      ( m1_pre_topc(sK2,sK0) ),
% 2.48/1.03      inference(subtyping,[status(esa)],[c_20]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_812,plain,
% 2.48/1.03      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_13,negated_conjecture,
% 2.48/1.03      ( m1_pre_topc(sK3,sK2) ),
% 2.48/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_301,negated_conjecture,
% 2.48/1.03      ( m1_pre_topc(sK3,sK2) ),
% 2.48/1.03      inference(subtyping,[status(esa)],[c_13]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_805,plain,
% 2.48/1.03      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_301]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_14,negated_conjecture,
% 2.48/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 2.48/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_300,negated_conjecture,
% 2.48/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 2.48/1.03      inference(subtyping,[status(esa)],[c_14]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_806,plain,
% 2.48/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_4,plain,
% 2.48/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.48/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.48/1.03      | ~ m1_pre_topc(X3,X4)
% 2.48/1.03      | ~ m1_pre_topc(X3,X1)
% 2.48/1.03      | ~ m1_pre_topc(X1,X4)
% 2.48/1.03      | v2_struct_0(X4)
% 2.48/1.03      | v2_struct_0(X2)
% 2.48/1.03      | ~ v1_funct_1(X0)
% 2.48/1.03      | ~ l1_pre_topc(X4)
% 2.48/1.03      | ~ l1_pre_topc(X2)
% 2.48/1.03      | ~ v2_pre_topc(X4)
% 2.48/1.03      | ~ v2_pre_topc(X2)
% 2.48/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.48/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_310,plain,
% 2.48/1.03      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 2.48/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 2.48/1.03      | ~ m1_pre_topc(X2_48,X0_48)
% 2.48/1.03      | ~ m1_pre_topc(X2_48,X3_48)
% 2.48/1.03      | ~ m1_pre_topc(X0_48,X3_48)
% 2.48/1.03      | v2_struct_0(X1_48)
% 2.48/1.03      | v2_struct_0(X3_48)
% 2.48/1.03      | ~ v1_funct_1(X0_49)
% 2.48/1.03      | ~ l1_pre_topc(X1_48)
% 2.48/1.03      | ~ l1_pre_topc(X3_48)
% 2.48/1.03      | ~ v2_pre_topc(X1_48)
% 2.48/1.03      | ~ v2_pre_topc(X3_48)
% 2.48/1.03      | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49) ),
% 2.48/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_796,plain,
% 2.48/1.03      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)
% 2.48/1.03      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 2.48/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 2.48/1.03      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 2.48/1.03      | m1_pre_topc(X2_48,X3_48) != iProver_top
% 2.48/1.03      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 2.48/1.03      | v2_struct_0(X1_48) = iProver_top
% 2.48/1.03      | v2_struct_0(X3_48) = iProver_top
% 2.48/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.48/1.03      | l1_pre_topc(X1_48) != iProver_top
% 2.48/1.03      | l1_pre_topc(X3_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(X1_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(X3_48) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_11,plain,
% 2.48/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.48/1.03      | ~ m1_pre_topc(X2,X0)
% 2.48/1.03      | m1_pre_topc(X2,X1)
% 2.48/1.03      | ~ l1_pre_topc(X1)
% 2.48/1.03      | ~ v2_pre_topc(X1) ),
% 2.48/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_303,plain,
% 2.48/1.03      ( ~ m1_pre_topc(X0_48,X1_48)
% 2.48/1.03      | ~ m1_pre_topc(X2_48,X0_48)
% 2.48/1.03      | m1_pre_topc(X2_48,X1_48)
% 2.48/1.03      | ~ l1_pre_topc(X1_48)
% 2.48/1.03      | ~ v2_pre_topc(X1_48) ),
% 2.48/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_803,plain,
% 2.48/1.03      ( m1_pre_topc(X0_48,X1_48) != iProver_top
% 2.48/1.03      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 2.48/1.03      | m1_pre_topc(X2_48,X1_48) = iProver_top
% 2.48/1.03      | l1_pre_topc(X1_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(X1_48) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1041,plain,
% 2.48/1.03      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)
% 2.48/1.03      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 2.48/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 2.48/1.03      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 2.48/1.03      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 2.48/1.03      | v2_struct_0(X1_48) = iProver_top
% 2.48/1.03      | v2_struct_0(X3_48) = iProver_top
% 2.48/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.48/1.03      | l1_pre_topc(X1_48) != iProver_top
% 2.48/1.03      | l1_pre_topc(X3_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(X1_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(X3_48) != iProver_top ),
% 2.48/1.03      inference(forward_subsumption_resolution,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_796,c_803]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3111,plain,
% 2.48/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK4)
% 2.48/1.03      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.48/1.03      | m1_pre_topc(X0_48,sK2) != iProver_top
% 2.48/1.03      | m1_pre_topc(sK2,X1_48) != iProver_top
% 2.48/1.03      | v2_struct_0(X1_48) = iProver_top
% 2.48/1.03      | v2_struct_0(sK1) = iProver_top
% 2.48/1.03      | v1_funct_1(sK4) != iProver_top
% 2.48/1.03      | l1_pre_topc(X1_48) != iProver_top
% 2.48/1.03      | l1_pre_topc(sK1) != iProver_top
% 2.48/1.03      | v2_pre_topc(X1_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_806,c_1041]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_24,negated_conjecture,
% 2.48/1.03      ( ~ v2_struct_0(sK1) ),
% 2.48/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_31,plain,
% 2.48/1.03      ( v2_struct_0(sK1) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_23,negated_conjecture,
% 2.48/1.03      ( v2_pre_topc(sK1) ),
% 2.48/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_32,plain,
% 2.48/1.03      ( v2_pre_topc(sK1) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_22,negated_conjecture,
% 2.48/1.03      ( l1_pre_topc(sK1) ),
% 2.48/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_33,plain,
% 2.48/1.03      ( l1_pre_topc(sK1) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_17,negated_conjecture,
% 2.48/1.03      ( v1_funct_1(sK4) ),
% 2.48/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_38,plain,
% 2.48/1.03      ( v1_funct_1(sK4) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_16,negated_conjecture,
% 2.48/1.03      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 2.48/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_39,plain,
% 2.48/1.03      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3303,plain,
% 2.48/1.03      ( v2_pre_topc(X1_48) != iProver_top
% 2.48/1.03      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK4)
% 2.48/1.03      | m1_pre_topc(X0_48,sK2) != iProver_top
% 2.48/1.03      | m1_pre_topc(sK2,X1_48) != iProver_top
% 2.48/1.03      | v2_struct_0(X1_48) = iProver_top
% 2.48/1.03      | l1_pre_topc(X1_48) != iProver_top ),
% 2.48/1.03      inference(global_propositional_subsumption,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_3111,c_31,c_32,c_33,c_38,c_39]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3304,plain,
% 2.48/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK4)
% 2.48/1.03      | m1_pre_topc(X0_48,sK2) != iProver_top
% 2.48/1.03      | m1_pre_topc(sK2,X1_48) != iProver_top
% 2.48/1.03      | v2_struct_0(X1_48) = iProver_top
% 2.48/1.03      | l1_pre_topc(X1_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(X1_48) != iProver_top ),
% 2.48/1.03      inference(renaming,[status(thm)],[c_3303]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3315,plain,
% 2.48/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0_48,sK1,sK2,sK3,sK4)
% 2.48/1.03      | m1_pre_topc(sK2,X0_48) != iProver_top
% 2.48/1.03      | v2_struct_0(X0_48) = iProver_top
% 2.48/1.03      | l1_pre_topc(X0_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(X0_48) != iProver_top ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_805,c_3304]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3,plain,
% 2.48/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.48/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.48/1.03      | ~ m1_pre_topc(X3,X1)
% 2.48/1.03      | v2_struct_0(X1)
% 2.48/1.03      | v2_struct_0(X2)
% 2.48/1.03      | ~ v1_funct_1(X0)
% 2.48/1.03      | ~ l1_pre_topc(X1)
% 2.48/1.03      | ~ l1_pre_topc(X2)
% 2.48/1.03      | ~ v2_pre_topc(X1)
% 2.48/1.03      | ~ v2_pre_topc(X2)
% 2.48/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.48/1.03      inference(cnf_transformation,[],[f36]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_311,plain,
% 2.48/1.03      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 2.48/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 2.48/1.03      | ~ m1_pre_topc(X2_48,X0_48)
% 2.48/1.03      | v2_struct_0(X1_48)
% 2.48/1.03      | v2_struct_0(X0_48)
% 2.48/1.03      | ~ v1_funct_1(X0_49)
% 2.48/1.03      | ~ l1_pre_topc(X1_48)
% 2.48/1.03      | ~ l1_pre_topc(X0_48)
% 2.48/1.03      | ~ v2_pre_topc(X1_48)
% 2.48/1.03      | ~ v2_pre_topc(X0_48)
% 2.48/1.03      | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48) ),
% 2.48/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_795,plain,
% 2.48/1.03      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48)
% 2.48/1.03      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 2.48/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 2.48/1.03      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 2.48/1.03      | v2_struct_0(X1_48) = iProver_top
% 2.48/1.03      | v2_struct_0(X0_48) = iProver_top
% 2.48/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.48/1.03      | l1_pre_topc(X1_48) != iProver_top
% 2.48/1.03      | l1_pre_topc(X0_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(X1_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(X0_48) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2305,plain,
% 2.48/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK4,X0_48)
% 2.48/1.03      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.48/1.03      | m1_pre_topc(X0_48,sK2) != iProver_top
% 2.48/1.03      | v2_struct_0(sK2) = iProver_top
% 2.48/1.03      | v2_struct_0(sK1) = iProver_top
% 2.48/1.03      | v1_funct_1(sK4) != iProver_top
% 2.48/1.03      | l1_pre_topc(sK2) != iProver_top
% 2.48/1.03      | l1_pre_topc(sK1) != iProver_top
% 2.48/1.03      | v2_pre_topc(sK2) != iProver_top
% 2.48/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_806,c_795]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_26,negated_conjecture,
% 2.48/1.03      ( v2_pre_topc(sK0) ),
% 2.48/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_29,plain,
% 2.48/1.03      ( v2_pre_topc(sK0) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_25,negated_conjecture,
% 2.48/1.03      ( l1_pre_topc(sK0) ),
% 2.48/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_30,plain,
% 2.48/1.03      ( l1_pre_topc(sK0) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_21,negated_conjecture,
% 2.48/1.03      ( ~ v2_struct_0(sK2) ),
% 2.48/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_34,plain,
% 2.48/1.03      ( v2_struct_0(sK2) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_35,plain,
% 2.48/1.03      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_0,plain,
% 2.48/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.48/1.03      | ~ l1_pre_topc(X1)
% 2.48/1.03      | ~ v2_pre_topc(X1)
% 2.48/1.03      | v2_pre_topc(X0) ),
% 2.48/1.03      inference(cnf_transformation,[],[f33]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_314,plain,
% 2.48/1.03      ( ~ m1_pre_topc(X0_48,X1_48)
% 2.48/1.03      | ~ l1_pre_topc(X1_48)
% 2.48/1.03      | ~ v2_pre_topc(X1_48)
% 2.48/1.03      | v2_pre_topc(X0_48) ),
% 2.48/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_792,plain,
% 2.48/1.03      ( m1_pre_topc(X0_48,X1_48) != iProver_top
% 2.48/1.03      | l1_pre_topc(X1_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(X1_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(X0_48) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1310,plain,
% 2.48/1.03      ( l1_pre_topc(sK0) != iProver_top
% 2.48/1.03      | v2_pre_topc(sK2) = iProver_top
% 2.48/1.03      | v2_pre_topc(sK0) != iProver_top ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_812,c_792]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2,plain,
% 2.48/1.03      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.48/1.03      inference(cnf_transformation,[],[f35]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_312,plain,
% 2.48/1.03      ( ~ m1_pre_topc(X0_48,X1_48)
% 2.48/1.03      | ~ l1_pre_topc(X1_48)
% 2.48/1.03      | l1_pre_topc(X0_48) ),
% 2.48/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1255,plain,
% 2.48/1.03      ( ~ m1_pre_topc(sK2,X0_48)
% 2.48/1.03      | ~ l1_pre_topc(X0_48)
% 2.48/1.03      | l1_pre_topc(sK2) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_312]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1360,plain,
% 2.48/1.03      ( ~ m1_pre_topc(sK2,sK0) | l1_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_1255]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1361,plain,
% 2.48/1.03      ( m1_pre_topc(sK2,sK0) != iProver_top
% 2.48/1.03      | l1_pre_topc(sK2) = iProver_top
% 2.48/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_1360]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2782,plain,
% 2.48/1.03      ( m1_pre_topc(X0_48,sK2) != iProver_top
% 2.48/1.03      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK4,X0_48) ),
% 2.48/1.03      inference(global_propositional_subsumption,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_2305,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_38,c_39,
% 2.48/1.03                 c_1310,c_1361]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2783,plain,
% 2.48/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK4,X0_48)
% 2.48/1.03      | m1_pre_topc(X0_48,sK2) != iProver_top ),
% 2.48/1.03      inference(renaming,[status(thm)],[c_2782]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2790,plain,
% 2.48/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK4,sK3) ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_805,c_2783]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3316,plain,
% 2.48/1.03      ( k3_tmap_1(X0_48,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
% 2.48/1.03      | m1_pre_topc(sK2,X0_48) != iProver_top
% 2.48/1.03      | v2_struct_0(X0_48) = iProver_top
% 2.48/1.03      | l1_pre_topc(X0_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(X0_48) != iProver_top ),
% 2.48/1.03      inference(light_normalisation,[status(thm)],[c_3315,c_2790]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3701,plain,
% 2.48/1.03      ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
% 2.48/1.03      | v2_struct_0(sK0) = iProver_top
% 2.48/1.03      | l1_pre_topc(sK0) != iProver_top
% 2.48/1.03      | v2_pre_topc(sK0) != iProver_top ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_812,c_3316]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_27,negated_conjecture,
% 2.48/1.03      ( ~ v2_struct_0(sK0) ),
% 2.48/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_28,plain,
% 2.48/1.03      ( v2_struct_0(sK0) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3704,plain,
% 2.48/1.03      ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) ),
% 2.48/1.03      inference(global_propositional_subsumption,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_3701,c_28,c_29,c_30]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_12,negated_conjecture,
% 2.48/1.03      ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
% 2.48/1.03      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
% 2.48/1.03      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.48/1.03      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
% 2.48/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_302,negated_conjecture,
% 2.48/1.03      ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
% 2.48/1.03      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
% 2.48/1.03      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.48/1.03      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
% 2.48/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_804,plain,
% 2.48/1.03      ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) != iProver_top
% 2.48/1.03      | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.48/1.03      | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.48/1.03      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3707,plain,
% 2.48/1.03      ( v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) != iProver_top
% 2.48/1.03      | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.48/1.03      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.48/1.03      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
% 2.48/1.03      inference(demodulation,[status(thm)],[c_3704,c_804]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_5,plain,
% 2.48/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.48/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.48/1.03      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 2.48/1.03      | ~ v1_funct_1(X0)
% 2.48/1.03      | ~ l1_struct_0(X3)
% 2.48/1.03      | ~ l1_struct_0(X2)
% 2.48/1.03      | ~ l1_struct_0(X1) ),
% 2.48/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_309,plain,
% 2.48/1.03      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 2.48/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 2.48/1.03      | m1_subset_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
% 2.48/1.03      | ~ v1_funct_1(X0_49)
% 2.48/1.03      | ~ l1_struct_0(X2_48)
% 2.48/1.03      | ~ l1_struct_0(X1_48)
% 2.48/1.03      | ~ l1_struct_0(X0_48) ),
% 2.48/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1265,plain,
% 2.48/1.03      ( ~ v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(sK1))
% 2.48/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.48/1.03      | m1_subset_1(k2_tmap_1(sK2,sK1,X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1))))
% 2.48/1.03      | ~ v1_funct_1(X0_49)
% 2.48/1.03      | ~ l1_struct_0(X0_48)
% 2.48/1.03      | ~ l1_struct_0(sK2)
% 2.48/1.03      | ~ l1_struct_0(sK1) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_309]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1867,plain,
% 2.48/1.03      ( ~ v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(sK1))
% 2.48/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.48/1.03      | m1_subset_1(k2_tmap_1(sK2,sK1,X0_49,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.48/1.03      | ~ v1_funct_1(X0_49)
% 2.48/1.03      | ~ l1_struct_0(sK3)
% 2.48/1.03      | ~ l1_struct_0(sK2)
% 2.48/1.03      | ~ l1_struct_0(sK1) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_1265]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1868,plain,
% 2.48/1.03      ( v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.48/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.48/1.03      | m1_subset_1(k2_tmap_1(sK2,sK1,X0_49,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 2.48/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.48/1.03      | l1_struct_0(sK3) != iProver_top
% 2.48/1.03      | l1_struct_0(sK2) != iProver_top
% 2.48/1.03      | l1_struct_0(sK1) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_1867]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1870,plain,
% 2.48/1.03      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.48/1.03      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 2.48/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.48/1.03      | v1_funct_1(sK4) != iProver_top
% 2.48/1.03      | l1_struct_0(sK3) != iProver_top
% 2.48/1.03      | l1_struct_0(sK2) != iProver_top
% 2.48/1.03      | l1_struct_0(sK1) != iProver_top ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_1868]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1,plain,
% 2.48/1.03      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.48/1.03      inference(cnf_transformation,[],[f34]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_313,plain,
% 2.48/1.03      ( l1_struct_0(X0_48) | ~ l1_pre_topc(X0_48) ),
% 2.48/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1691,plain,
% 2.48/1.03      ( l1_struct_0(sK3) | ~ l1_pre_topc(sK3) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_313]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1692,plain,
% 2.48/1.03      ( l1_struct_0(sK3) = iProver_top
% 2.48/1.03      | l1_pre_topc(sK3) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_1691]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_794,plain,
% 2.48/1.03      ( m1_pre_topc(X0_48,X1_48) != iProver_top
% 2.48/1.03      | l1_pre_topc(X1_48) != iProver_top
% 2.48/1.03      | l1_pre_topc(X0_48) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_312]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1586,plain,
% 2.48/1.03      ( l1_pre_topc(sK3) = iProver_top
% 2.48/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_805,c_794]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1280,plain,
% 2.48/1.03      ( l1_struct_0(sK2) | ~ l1_pre_topc(sK2) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_313]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1281,plain,
% 2.48/1.03      ( l1_struct_0(sK2) = iProver_top
% 2.48/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_1280]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_8,plain,
% 2.48/1.03      ( ~ v5_pre_topc(X0,X1,X2)
% 2.48/1.03      | v5_pre_topc(k2_tmap_1(X1,X2,X0,X3),X3,X2)
% 2.48/1.03      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.48/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.48/1.03      | ~ m1_pre_topc(X3,X1)
% 2.48/1.03      | v2_struct_0(X1)
% 2.48/1.03      | v2_struct_0(X2)
% 2.48/1.03      | v2_struct_0(X3)
% 2.48/1.03      | ~ v1_funct_1(X0)
% 2.48/1.03      | ~ l1_pre_topc(X1)
% 2.48/1.03      | ~ l1_pre_topc(X2)
% 2.48/1.03      | ~ v2_pre_topc(X1)
% 2.48/1.03      | ~ v2_pre_topc(X2) ),
% 2.48/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_306,plain,
% 2.48/1.03      ( ~ v5_pre_topc(X0_49,X0_48,X1_48)
% 2.48/1.03      | v5_pre_topc(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),X2_48,X1_48)
% 2.48/1.03      | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 2.48/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 2.48/1.03      | ~ m1_pre_topc(X2_48,X0_48)
% 2.48/1.03      | v2_struct_0(X1_48)
% 2.48/1.03      | v2_struct_0(X2_48)
% 2.48/1.03      | v2_struct_0(X0_48)
% 2.48/1.03      | ~ v1_funct_1(X0_49)
% 2.48/1.03      | ~ l1_pre_topc(X1_48)
% 2.48/1.03      | ~ l1_pre_topc(X0_48)
% 2.48/1.03      | ~ v2_pre_topc(X1_48)
% 2.48/1.03      | ~ v2_pre_topc(X0_48) ),
% 2.48/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1215,plain,
% 2.48/1.03      ( ~ v5_pre_topc(X0_49,sK2,X0_48)
% 2.48/1.03      | v5_pre_topc(k2_tmap_1(sK2,X0_48,X0_49,sK3),sK3,X0_48)
% 2.48/1.03      | ~ v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(X0_48))
% 2.48/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_48))))
% 2.48/1.03      | ~ m1_pre_topc(sK3,sK2)
% 2.48/1.03      | v2_struct_0(X0_48)
% 2.48/1.03      | v2_struct_0(sK3)
% 2.48/1.03      | v2_struct_0(sK2)
% 2.48/1.03      | ~ v1_funct_1(X0_49)
% 2.48/1.03      | ~ l1_pre_topc(X0_48)
% 2.48/1.03      | ~ l1_pre_topc(sK2)
% 2.48/1.03      | ~ v2_pre_topc(X0_48)
% 2.48/1.03      | ~ v2_pre_topc(sK2) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_306]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1216,plain,
% 2.48/1.03      ( v5_pre_topc(X0_49,sK2,X0_48) != iProver_top
% 2.48/1.03      | v5_pre_topc(k2_tmap_1(sK2,X0_48,X0_49,sK3),sK3,X0_48) = iProver_top
% 2.48/1.03      | v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(X0_48)) != iProver_top
% 2.48/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_48)))) != iProver_top
% 2.48/1.03      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.48/1.03      | v2_struct_0(X0_48) = iProver_top
% 2.48/1.03      | v2_struct_0(sK3) = iProver_top
% 2.48/1.03      | v2_struct_0(sK2) = iProver_top
% 2.48/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.48/1.03      | l1_pre_topc(X0_48) != iProver_top
% 2.48/1.03      | l1_pre_topc(sK2) != iProver_top
% 2.48/1.03      | v2_pre_topc(X0_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(sK2) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_1215]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1218,plain,
% 2.48/1.03      ( v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) = iProver_top
% 2.48/1.03      | v5_pre_topc(sK4,sK2,sK1) != iProver_top
% 2.48/1.03      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.48/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.48/1.03      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.48/1.03      | v2_struct_0(sK3) = iProver_top
% 2.48/1.03      | v2_struct_0(sK2) = iProver_top
% 2.48/1.03      | v2_struct_0(sK1) = iProver_top
% 2.48/1.03      | v1_funct_1(sK4) != iProver_top
% 2.48/1.03      | l1_pre_topc(sK2) != iProver_top
% 2.48/1.03      | l1_pre_topc(sK1) != iProver_top
% 2.48/1.03      | v2_pre_topc(sK2) != iProver_top
% 2.48/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_1216]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_9,plain,
% 2.48/1.03      ( ~ v5_pre_topc(X0,X1,X2)
% 2.48/1.03      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.48/1.03      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 2.48/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.48/1.03      | ~ m1_pre_topc(X3,X1)
% 2.48/1.03      | v2_struct_0(X1)
% 2.48/1.03      | v2_struct_0(X2)
% 2.48/1.03      | v2_struct_0(X3)
% 2.48/1.03      | ~ v1_funct_1(X0)
% 2.48/1.03      | ~ l1_pre_topc(X1)
% 2.48/1.03      | ~ l1_pre_topc(X2)
% 2.48/1.03      | ~ v2_pre_topc(X1)
% 2.48/1.03      | ~ v2_pre_topc(X2) ),
% 2.48/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_305,plain,
% 2.48/1.03      ( ~ v5_pre_topc(X0_49,X0_48,X1_48)
% 2.48/1.03      | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 2.48/1.03      | v1_funct_2(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),u1_struct_0(X2_48),u1_struct_0(X1_48))
% 2.48/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 2.48/1.03      | ~ m1_pre_topc(X2_48,X0_48)
% 2.48/1.03      | v2_struct_0(X1_48)
% 2.48/1.03      | v2_struct_0(X2_48)
% 2.48/1.03      | v2_struct_0(X0_48)
% 2.48/1.03      | ~ v1_funct_1(X0_49)
% 2.48/1.03      | ~ l1_pre_topc(X1_48)
% 2.48/1.03      | ~ l1_pre_topc(X0_48)
% 2.48/1.03      | ~ v2_pre_topc(X1_48)
% 2.48/1.03      | ~ v2_pre_topc(X0_48) ),
% 2.48/1.03      inference(subtyping,[status(esa)],[c_9]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1200,plain,
% 2.48/1.03      ( ~ v5_pre_topc(X0_49,sK2,X0_48)
% 2.48/1.03      | ~ v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(X0_48))
% 2.48/1.03      | v1_funct_2(k2_tmap_1(sK2,X0_48,X0_49,sK3),u1_struct_0(sK3),u1_struct_0(X0_48))
% 2.48/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_48))))
% 2.48/1.03      | ~ m1_pre_topc(sK3,sK2)
% 2.48/1.03      | v2_struct_0(X0_48)
% 2.48/1.03      | v2_struct_0(sK3)
% 2.48/1.03      | v2_struct_0(sK2)
% 2.48/1.03      | ~ v1_funct_1(X0_49)
% 2.48/1.03      | ~ l1_pre_topc(X0_48)
% 2.48/1.03      | ~ l1_pre_topc(sK2)
% 2.48/1.03      | ~ v2_pre_topc(X0_48)
% 2.48/1.03      | ~ v2_pre_topc(sK2) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_305]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1201,plain,
% 2.48/1.03      ( v5_pre_topc(X0_49,sK2,X0_48) != iProver_top
% 2.48/1.03      | v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(X0_48)) != iProver_top
% 2.48/1.03      | v1_funct_2(k2_tmap_1(sK2,X0_48,X0_49,sK3),u1_struct_0(sK3),u1_struct_0(X0_48)) = iProver_top
% 2.48/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_48)))) != iProver_top
% 2.48/1.03      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.48/1.03      | v2_struct_0(X0_48) = iProver_top
% 2.48/1.03      | v2_struct_0(sK3) = iProver_top
% 2.48/1.03      | v2_struct_0(sK2) = iProver_top
% 2.48/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.48/1.03      | l1_pre_topc(X0_48) != iProver_top
% 2.48/1.03      | l1_pre_topc(sK2) != iProver_top
% 2.48/1.03      | v2_pre_topc(X0_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(sK2) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_1200]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1203,plain,
% 2.48/1.03      ( v5_pre_topc(sK4,sK2,sK1) != iProver_top
% 2.48/1.03      | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 2.48/1.03      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.48/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.48/1.03      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.48/1.03      | v2_struct_0(sK3) = iProver_top
% 2.48/1.03      | v2_struct_0(sK2) = iProver_top
% 2.48/1.03      | v2_struct_0(sK1) = iProver_top
% 2.48/1.03      | v1_funct_1(sK4) != iProver_top
% 2.48/1.03      | l1_pre_topc(sK2) != iProver_top
% 2.48/1.03      | l1_pre_topc(sK1) != iProver_top
% 2.48/1.03      | v2_pre_topc(sK2) != iProver_top
% 2.48/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_1201]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_10,plain,
% 2.48/1.03      ( ~ v5_pre_topc(X0,X1,X2)
% 2.48/1.03      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.48/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.48/1.03      | ~ m1_pre_topc(X3,X1)
% 2.48/1.03      | v2_struct_0(X1)
% 2.48/1.03      | v2_struct_0(X2)
% 2.48/1.03      | v2_struct_0(X3)
% 2.48/1.03      | ~ v1_funct_1(X0)
% 2.48/1.03      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3))
% 2.48/1.03      | ~ l1_pre_topc(X1)
% 2.48/1.03      | ~ l1_pre_topc(X2)
% 2.48/1.03      | ~ v2_pre_topc(X1)
% 2.48/1.03      | ~ v2_pre_topc(X2) ),
% 2.48/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_304,plain,
% 2.48/1.03      ( ~ v5_pre_topc(X0_49,X0_48,X1_48)
% 2.48/1.03      | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 2.48/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 2.48/1.03      | ~ m1_pre_topc(X2_48,X0_48)
% 2.48/1.03      | v2_struct_0(X1_48)
% 2.48/1.03      | v2_struct_0(X2_48)
% 2.48/1.03      | v2_struct_0(X0_48)
% 2.48/1.03      | ~ v1_funct_1(X0_49)
% 2.48/1.03      | v1_funct_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48))
% 2.48/1.03      | ~ l1_pre_topc(X1_48)
% 2.48/1.03      | ~ l1_pre_topc(X0_48)
% 2.48/1.03      | ~ v2_pre_topc(X1_48)
% 2.48/1.03      | ~ v2_pre_topc(X0_48) ),
% 2.48/1.03      inference(subtyping,[status(esa)],[c_10]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1170,plain,
% 2.48/1.03      ( ~ v5_pre_topc(X0_49,sK2,X0_48)
% 2.48/1.03      | ~ v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(X0_48))
% 2.48/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_48))))
% 2.48/1.03      | ~ m1_pre_topc(sK3,sK2)
% 2.48/1.03      | v2_struct_0(X0_48)
% 2.48/1.03      | v2_struct_0(sK3)
% 2.48/1.03      | v2_struct_0(sK2)
% 2.48/1.03      | ~ v1_funct_1(X0_49)
% 2.48/1.03      | v1_funct_1(k2_tmap_1(sK2,X0_48,X0_49,sK3))
% 2.48/1.03      | ~ l1_pre_topc(X0_48)
% 2.48/1.03      | ~ l1_pre_topc(sK2)
% 2.48/1.03      | ~ v2_pre_topc(X0_48)
% 2.48/1.03      | ~ v2_pre_topc(sK2) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_304]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1171,plain,
% 2.48/1.03      ( v5_pre_topc(X0_49,sK2,X0_48) != iProver_top
% 2.48/1.03      | v1_funct_2(X0_49,u1_struct_0(sK2),u1_struct_0(X0_48)) != iProver_top
% 2.48/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_48)))) != iProver_top
% 2.48/1.03      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.48/1.03      | v2_struct_0(X0_48) = iProver_top
% 2.48/1.03      | v2_struct_0(sK3) = iProver_top
% 2.48/1.03      | v2_struct_0(sK2) = iProver_top
% 2.48/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.48/1.03      | v1_funct_1(k2_tmap_1(sK2,X0_48,X0_49,sK3)) = iProver_top
% 2.48/1.03      | l1_pre_topc(X0_48) != iProver_top
% 2.48/1.03      | l1_pre_topc(sK2) != iProver_top
% 2.48/1.03      | v2_pre_topc(X0_48) != iProver_top
% 2.48/1.03      | v2_pre_topc(sK2) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_1170]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1173,plain,
% 2.48/1.03      ( v5_pre_topc(sK4,sK2,sK1) != iProver_top
% 2.48/1.03      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.48/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.48/1.03      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.48/1.03      | v2_struct_0(sK3) = iProver_top
% 2.48/1.03      | v2_struct_0(sK2) = iProver_top
% 2.48/1.03      | v2_struct_0(sK1) = iProver_top
% 2.48/1.03      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) = iProver_top
% 2.48/1.03      | v1_funct_1(sK4) != iProver_top
% 2.48/1.03      | l1_pre_topc(sK2) != iProver_top
% 2.48/1.03      | l1_pre_topc(sK1) != iProver_top
% 2.48/1.03      | v2_pre_topc(sK2) != iProver_top
% 2.48/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_1171]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_70,plain,
% 2.48/1.03      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_72,plain,
% 2.48/1.03      ( l1_struct_0(sK1) = iProver_top
% 2.48/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_70]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_42,plain,
% 2.48/1.03      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_41,plain,
% 2.48/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_15,negated_conjecture,
% 2.48/1.03      ( v5_pre_topc(sK4,sK2,sK1) ),
% 2.48/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_40,plain,
% 2.48/1.03      ( v5_pre_topc(sK4,sK2,sK1) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_19,negated_conjecture,
% 2.48/1.03      ( ~ v2_struct_0(sK3) ),
% 2.48/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_36,plain,
% 2.48/1.03      ( v2_struct_0(sK3) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(contradiction,plain,
% 2.48/1.03      ( $false ),
% 2.48/1.03      inference(minisat,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_3707,c_1870,c_1692,c_1586,c_1361,c_1310,c_1281,c_1218,
% 2.48/1.03                 c_1203,c_1173,c_72,c_42,c_41,c_40,c_39,c_38,c_36,c_35,
% 2.48/1.03                 c_34,c_33,c_32,c_31,c_30,c_29]) ).
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.48/1.03  
% 2.48/1.03  ------                               Statistics
% 2.48/1.03  
% 2.48/1.03  ------ General
% 2.48/1.03  
% 2.48/1.03  abstr_ref_over_cycles:                  0
% 2.48/1.03  abstr_ref_under_cycles:                 0
% 2.48/1.03  gc_basic_clause_elim:                   0
% 2.48/1.03  forced_gc_time:                         0
% 2.48/1.03  parsing_time:                           0.01
% 2.48/1.03  unif_index_cands_time:                  0.
% 2.48/1.03  unif_index_add_time:                    0.
% 2.48/1.03  orderings_time:                         0.
% 2.48/1.03  out_proof_time:                         0.019
% 2.48/1.03  total_time:                             0.245
% 2.48/1.03  num_of_symbols:                         53
% 2.48/1.03  num_of_terms:                           3220
% 2.48/1.03  
% 2.48/1.03  ------ Preprocessing
% 2.48/1.03  
% 2.48/1.03  num_of_splits:                          0
% 2.48/1.03  num_of_split_atoms:                     0
% 2.48/1.03  num_of_reused_defs:                     0
% 2.48/1.03  num_eq_ax_congr_red:                    33
% 2.48/1.03  num_of_sem_filtered_clauses:            1
% 2.48/1.03  num_of_subtypes:                        5
% 2.48/1.03  monotx_restored_types:                  0
% 2.48/1.03  sat_num_of_epr_types:                   0
% 2.48/1.03  sat_num_of_non_cyclic_types:            0
% 2.48/1.03  sat_guarded_non_collapsed_types:        0
% 2.48/1.03  num_pure_diseq_elim:                    0
% 2.48/1.03  simp_replaced_by:                       0
% 2.48/1.03  res_preprocessed:                       99
% 2.48/1.03  prep_upred:                             0
% 2.48/1.03  prep_unflattend:                        0
% 2.48/1.03  smt_new_axioms:                         0
% 2.48/1.03  pred_elim_cands:                        9
% 2.48/1.03  pred_elim:                              0
% 2.48/1.03  pred_elim_cl:                           0
% 2.48/1.03  pred_elim_cycles:                       1
% 2.48/1.03  merged_defs:                            0
% 2.48/1.03  merged_defs_ncl:                        0
% 2.48/1.03  bin_hyper_res:                          0
% 2.48/1.03  prep_cycles:                            3
% 2.48/1.03  pred_elim_time:                         0.
% 2.48/1.03  splitting_time:                         0.
% 2.48/1.03  sem_filter_time:                        0.
% 2.48/1.03  monotx_time:                            0.
% 2.48/1.03  subtype_inf_time:                       0.001
% 2.48/1.03  
% 2.48/1.03  ------ Problem properties
% 2.48/1.03  
% 2.48/1.03  clauses:                                28
% 2.48/1.03  conjectures:                            16
% 2.48/1.03  epr:                                    17
% 2.48/1.03  horn:                                   23
% 2.48/1.03  ground:                                 16
% 2.48/1.03  unary:                                  15
% 2.48/1.03  binary:                                 1
% 2.48/1.03  lits:                                   117
% 2.48/1.03  lits_eq:                                2
% 2.48/1.03  fd_pure:                                0
% 2.48/1.03  fd_pseudo:                              0
% 2.48/1.03  fd_cond:                                0
% 2.48/1.03  fd_pseudo_cond:                         0
% 2.48/1.03  ac_symbols:                             0
% 2.48/1.03  
% 2.48/1.03  ------ Propositional Solver
% 2.48/1.03  
% 2.48/1.03  prop_solver_calls:                      25
% 2.48/1.03  prop_fast_solver_calls:                 1147
% 2.48/1.03  smt_solver_calls:                       0
% 2.48/1.03  smt_fast_solver_calls:                  0
% 2.48/1.03  prop_num_of_clauses:                    1097
% 2.48/1.03  prop_preprocess_simplified:             4089
% 2.48/1.03  prop_fo_subsumed:                       72
% 2.48/1.03  prop_solver_time:                       0.
% 2.48/1.03  smt_solver_time:                        0.
% 2.48/1.03  smt_fast_solver_time:                   0.
% 2.48/1.03  prop_fast_solver_time:                  0.
% 2.48/1.03  prop_unsat_core_time:                   0.
% 2.48/1.03  
% 2.48/1.03  ------ QBF
% 2.48/1.03  
% 2.48/1.03  qbf_q_res:                              0
% 2.48/1.03  qbf_num_tautologies:                    0
% 2.48/1.03  qbf_prep_cycles:                        0
% 2.48/1.03  
% 2.48/1.03  ------ BMC1
% 2.48/1.03  
% 2.48/1.03  bmc1_current_bound:                     -1
% 2.48/1.03  bmc1_last_solved_bound:                 -1
% 2.48/1.03  bmc1_unsat_core_size:                   -1
% 2.48/1.03  bmc1_unsat_core_parents_size:           -1
% 2.48/1.03  bmc1_merge_next_fun:                    0
% 2.48/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.48/1.03  
% 2.48/1.03  ------ Instantiation
% 2.48/1.03  
% 2.48/1.03  inst_num_of_clauses:                    361
% 2.48/1.03  inst_num_in_passive:                    94
% 2.48/1.03  inst_num_in_active:                     210
% 2.48/1.03  inst_num_in_unprocessed:                57
% 2.48/1.03  inst_num_of_loops:                      270
% 2.48/1.03  inst_num_of_learning_restarts:          0
% 2.48/1.03  inst_num_moves_active_passive:          56
% 2.48/1.03  inst_lit_activity:                      0
% 2.48/1.03  inst_lit_activity_moves:                0
% 2.48/1.03  inst_num_tautologies:                   0
% 2.48/1.03  inst_num_prop_implied:                  0
% 2.48/1.03  inst_num_existing_simplified:           0
% 2.48/1.03  inst_num_eq_res_simplified:             0
% 2.48/1.03  inst_num_child_elim:                    0
% 2.48/1.03  inst_num_of_dismatching_blockings:      63
% 2.48/1.03  inst_num_of_non_proper_insts:           386
% 2.48/1.03  inst_num_of_duplicates:                 0
% 2.48/1.03  inst_inst_num_from_inst_to_res:         0
% 2.48/1.03  inst_dismatching_checking_time:         0.
% 2.48/1.03  
% 2.48/1.03  ------ Resolution
% 2.48/1.03  
% 2.48/1.03  res_num_of_clauses:                     0
% 2.48/1.03  res_num_in_passive:                     0
% 2.48/1.03  res_num_in_active:                      0
% 2.48/1.03  res_num_of_loops:                       102
% 2.48/1.03  res_forward_subset_subsumed:            28
% 2.48/1.03  res_backward_subset_subsumed:           0
% 2.48/1.03  res_forward_subsumed:                   0
% 2.48/1.03  res_backward_subsumed:                  0
% 2.48/1.03  res_forward_subsumption_resolution:     0
% 2.48/1.03  res_backward_subsumption_resolution:    0
% 2.48/1.03  res_clause_to_clause_subsumption:       194
% 2.48/1.03  res_orphan_elimination:                 0
% 2.48/1.03  res_tautology_del:                      46
% 2.48/1.03  res_num_eq_res_simplified:              0
% 2.48/1.03  res_num_sel_changes:                    0
% 2.48/1.03  res_moves_from_active_to_pass:          0
% 2.48/1.03  
% 2.48/1.03  ------ Superposition
% 2.48/1.03  
% 2.48/1.03  sup_time_total:                         0.
% 2.48/1.03  sup_time_generating:                    0.
% 2.48/1.03  sup_time_sim_full:                      0.
% 2.48/1.03  sup_time_sim_immed:                     0.
% 2.48/1.03  
% 2.48/1.03  sup_num_of_clauses:                     59
% 2.48/1.03  sup_num_in_active:                      52
% 2.48/1.03  sup_num_in_passive:                     7
% 2.48/1.03  sup_num_of_loops:                       53
% 2.48/1.03  sup_fw_superposition:                   30
% 2.48/1.03  sup_bw_superposition:                   4
% 2.48/1.03  sup_immediate_simplified:               1
% 2.48/1.03  sup_given_eliminated:                   0
% 2.48/1.03  comparisons_done:                       0
% 2.48/1.03  comparisons_avoided:                    0
% 2.48/1.03  
% 2.48/1.03  ------ Simplifications
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  sim_fw_subset_subsumed:                 0
% 2.48/1.03  sim_bw_subset_subsumed:                 1
% 2.48/1.03  sim_fw_subsumed:                        0
% 2.48/1.03  sim_bw_subsumed:                        0
% 2.48/1.03  sim_fw_subsumption_res:                 3
% 2.48/1.03  sim_bw_subsumption_res:                 0
% 2.48/1.03  sim_tautology_del:                      0
% 2.48/1.03  sim_eq_tautology_del:                   0
% 2.48/1.03  sim_eq_res_simp:                        0
% 2.48/1.03  sim_fw_demodulated:                     0
% 2.48/1.03  sim_bw_demodulated:                     1
% 2.48/1.03  sim_light_normalised:                   1
% 2.48/1.03  sim_joinable_taut:                      0
% 2.48/1.03  sim_joinable_simp:                      0
% 2.48/1.03  sim_ac_normalised:                      0
% 2.48/1.03  sim_smt_subsumption:                    0
% 2.48/1.03  
%------------------------------------------------------------------------------
