%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:42 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 837 expanded)
%              Number of clauses        :   99 ( 200 expanded)
%              Number of leaves         :   17 ( 330 expanded)
%              Depth                    :   17
%              Number of atoms          : 1018 (13204 expanded)
%              Number of equality atoms :  247 ( 331 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(negated_conjecture,[],[f12])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f32,f37,f36,f35,f34,f33])).

fof(f64,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f50,plain,(
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

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1002,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1612,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1002])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1009,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1605,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1009])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1008,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1606,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f51])).

cnf(c_1016,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,X0_51)
    | ~ m1_pre_topc(X2_51,X3_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X3_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X3_51)
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_53,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_53) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1598,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_53,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_53)
    | v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X2_51,X3_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X3_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X3_51) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1011,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X0_51)
    | m1_pre_topc(X2_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1603,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1011])).

cnf(c_1874,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_53,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_53)
    | v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X3_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X3_51) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1598,c_1603])).

cnf(c_4124,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1606,c_1874])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_37,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_38,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_39,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_44,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_45,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4247,plain,
    ( l1_pre_topc(X1_51) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK4)
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4124,c_37,c_38,c_39,c_44,c_45])).

cnf(c_4248,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK4)
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_4247])).

cnf(c_4259,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0_51,sK1,sK2,sK3,sK4)
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_4248])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f50])).

cnf(c_1017,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,X0_51)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_53,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_53,X2_51) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1597,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_53,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_53,X2_51)
    | v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1017])).

cnf(c_2989,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK4,X0_51)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1606,c_1597])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_35,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_36,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_40,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_41,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1018,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2120,plain,
    ( ~ m1_pre_topc(sK2,X0_51)
    | ~ l1_pre_topc(X0_51)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1018])).

cnf(c_2231,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2120])).

cnf(c_2232,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2231])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1019,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1595,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1019])).

cnf(c_2463,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_1595])).

cnf(c_3490,plain,
    ( m1_pre_topc(X0_51,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2989,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_44,c_45,c_2232,c_2463])).

cnf(c_3491,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK4,X0_51)
    | m1_pre_topc(X0_51,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3490])).

cnf(c_3498,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_1605,c_3491])).

cnf(c_4260,plain,
    ( k3_tmap_1(X0_51,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4259,c_3498])).

cnf(c_4364,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_4260])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_34,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4367,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4364,c_34,c_35,c_36])).

cnf(c_18,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1010,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1604,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1010])).

cnf(c_4370,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4367,c_1604])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1024,plain,
    ( ~ v1_funct_2(X0_53,X0_52,X1_52)
    | ~ r1_tarski(X2_52,X0_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | m1_subset_1(k2_partfun1(X0_52,X1_52,X0_53,X2_52),k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52)))
    | ~ v1_funct_1(X0_53)
    | k1_xboole_0 = X1_52 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1590,plain,
    ( k1_xboole_0 = X0_52
    | v1_funct_2(X0_53,X1_52,X0_52) != iProver_top
    | r1_tarski(X2_52,X1_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) != iProver_top
    | m1_subset_1(k2_partfun1(X1_52,X0_52,X0_53,X2_52),k1_zfmisc_1(k2_zfmisc_1(X2_52,X0_52))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_3501,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3498,c_1590])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_1015,plain,
    ( ~ v5_pre_topc(X0_53,X0_51,X1_51)
    | v5_pre_topc(k2_tmap_1(X0_51,X1_51,X0_53,X2_51),X2_51,X1_51)
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,X0_51)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2055,plain,
    ( ~ v5_pre_topc(X0_53,sK2,X0_51)
    | v5_pre_topc(k2_tmap_1(sK2,X0_51,X0_53,sK3),sK3,X0_51)
    | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_51))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_1015])).

cnf(c_2056,plain,
    ( v5_pre_topc(X0_53,sK2,X0_51) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_51,X0_53,sK3),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_51)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2055])).

cnf(c_2058,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) = iProver_top
    | v5_pre_topc(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2056])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f53])).

cnf(c_1014,plain,
    ( ~ v5_pre_topc(X0_53,X0_51,X1_51)
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | v1_funct_2(k2_tmap_1(X0_51,X1_51,X0_53,X2_51),u1_struct_0(X2_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,X0_51)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2040,plain,
    ( ~ v5_pre_topc(X0_53,sK2,X0_51)
    | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_51))
    | v1_funct_2(k2_tmap_1(sK2,X0_51,X0_53,sK3),u1_struct_0(sK3),u1_struct_0(X0_51))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_2041,plain,
    ( v5_pre_topc(X0_53,sK2,X0_51) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_51)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_51,X0_53,sK3),u1_struct_0(sK3),u1_struct_0(X0_51)) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2040])).

cnf(c_2043,plain,
    ( v5_pre_topc(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2041])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f52])).

cnf(c_1013,plain,
    ( ~ v5_pre_topc(X0_53,X0_51,X1_51)
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,X0_51)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k2_tmap_1(X0_51,X1_51,X0_53,X2_51)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2010,plain,
    ( ~ v5_pre_topc(X0_53,sK2,X0_51)
    | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_51))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k2_tmap_1(sK2,X0_51,X0_53,sK3)) ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_2011,plain,
    ( v5_pre_topc(X0_53,sK2,X0_51) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_51)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_51,X0_53,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2010])).

cnf(c_2013,plain,
    ( v5_pre_topc(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2011])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1012,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | r1_tarski(u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1969,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_1970,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1969])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_10,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_353,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_371,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_353])).

cnf(c_994,plain,
    ( v2_struct_0(X0_51)
    | ~ l1_pre_topc(X0_51)
    | u1_struct_0(X0_51) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_371])).

cnf(c_1106,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_48,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_47,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_46,plain,
    ( v5_pre_topc(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_42,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4370,c_3501,c_2463,c_2232,c_2058,c_2043,c_2013,c_1970,c_1106,c_48,c_47,c_46,c_45,c_44,c_42,c_41,c_40,c_39,c_28,c_38,c_37,c_30,c_36,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.32/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/0.99  
% 2.32/0.99  ------  iProver source info
% 2.32/0.99  
% 2.32/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.32/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/0.99  git: non_committed_changes: false
% 2.32/0.99  git: last_make_outside_of_git: false
% 2.32/0.99  
% 2.32/0.99  ------ 
% 2.32/0.99  
% 2.32/0.99  ------ Input Options
% 2.32/0.99  
% 2.32/0.99  --out_options                           all
% 2.32/0.99  --tptp_safe_out                         true
% 2.32/0.99  --problem_path                          ""
% 2.32/0.99  --include_path                          ""
% 2.32/0.99  --clausifier                            res/vclausify_rel
% 2.32/0.99  --clausifier_options                    --mode clausify
% 2.32/0.99  --stdin                                 false
% 2.32/0.99  --stats_out                             all
% 2.32/0.99  
% 2.32/0.99  ------ General Options
% 2.32/0.99  
% 2.32/0.99  --fof                                   false
% 2.32/0.99  --time_out_real                         305.
% 2.32/0.99  --time_out_virtual                      -1.
% 2.32/0.99  --symbol_type_check                     false
% 2.32/0.99  --clausify_out                          false
% 2.32/0.99  --sig_cnt_out                           false
% 2.32/0.99  --trig_cnt_out                          false
% 2.32/0.99  --trig_cnt_out_tolerance                1.
% 2.32/0.99  --trig_cnt_out_sk_spl                   false
% 2.32/0.99  --abstr_cl_out                          false
% 2.32/0.99  
% 2.32/0.99  ------ Global Options
% 2.32/0.99  
% 2.32/0.99  --schedule                              default
% 2.32/0.99  --add_important_lit                     false
% 2.32/0.99  --prop_solver_per_cl                    1000
% 2.32/0.99  --min_unsat_core                        false
% 2.32/0.99  --soft_assumptions                      false
% 2.32/0.99  --soft_lemma_size                       3
% 2.32/0.99  --prop_impl_unit_size                   0
% 2.32/0.99  --prop_impl_unit                        []
% 2.32/0.99  --share_sel_clauses                     true
% 2.32/0.99  --reset_solvers                         false
% 2.32/0.99  --bc_imp_inh                            [conj_cone]
% 2.32/0.99  --conj_cone_tolerance                   3.
% 2.32/0.99  --extra_neg_conj                        none
% 2.32/0.99  --large_theory_mode                     true
% 2.32/0.99  --prolific_symb_bound                   200
% 2.32/0.99  --lt_threshold                          2000
% 2.32/0.99  --clause_weak_htbl                      true
% 2.32/0.99  --gc_record_bc_elim                     false
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing Options
% 2.32/0.99  
% 2.32/0.99  --preprocessing_flag                    true
% 2.32/0.99  --time_out_prep_mult                    0.1
% 2.32/0.99  --splitting_mode                        input
% 2.32/0.99  --splitting_grd                         true
% 2.32/0.99  --splitting_cvd                         false
% 2.32/0.99  --splitting_cvd_svl                     false
% 2.32/0.99  --splitting_nvd                         32
% 2.32/0.99  --sub_typing                            true
% 2.32/0.99  --prep_gs_sim                           true
% 2.32/0.99  --prep_unflatten                        true
% 2.32/0.99  --prep_res_sim                          true
% 2.32/0.99  --prep_upred                            true
% 2.32/0.99  --prep_sem_filter                       exhaustive
% 2.32/0.99  --prep_sem_filter_out                   false
% 2.32/0.99  --pred_elim                             true
% 2.32/0.99  --res_sim_input                         true
% 2.32/0.99  --eq_ax_congr_red                       true
% 2.32/0.99  --pure_diseq_elim                       true
% 2.32/0.99  --brand_transform                       false
% 2.32/0.99  --non_eq_to_eq                          false
% 2.32/0.99  --prep_def_merge                        true
% 2.32/0.99  --prep_def_merge_prop_impl              false
% 2.32/0.99  --prep_def_merge_mbd                    true
% 2.32/0.99  --prep_def_merge_tr_red                 false
% 2.32/0.99  --prep_def_merge_tr_cl                  false
% 2.32/0.99  --smt_preprocessing                     true
% 2.32/0.99  --smt_ac_axioms                         fast
% 2.32/0.99  --preprocessed_out                      false
% 2.32/0.99  --preprocessed_stats                    false
% 2.32/0.99  
% 2.32/0.99  ------ Abstraction refinement Options
% 2.32/0.99  
% 2.32/0.99  --abstr_ref                             []
% 2.32/0.99  --abstr_ref_prep                        false
% 2.32/0.99  --abstr_ref_until_sat                   false
% 2.32/0.99  --abstr_ref_sig_restrict                funpre
% 2.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/0.99  --abstr_ref_under                       []
% 2.32/0.99  
% 2.32/0.99  ------ SAT Options
% 2.32/0.99  
% 2.32/0.99  --sat_mode                              false
% 2.32/0.99  --sat_fm_restart_options                ""
% 2.32/0.99  --sat_gr_def                            false
% 2.32/0.99  --sat_epr_types                         true
% 2.32/0.99  --sat_non_cyclic_types                  false
% 2.32/0.99  --sat_finite_models                     false
% 2.32/0.99  --sat_fm_lemmas                         false
% 2.32/0.99  --sat_fm_prep                           false
% 2.32/0.99  --sat_fm_uc_incr                        true
% 2.32/0.99  --sat_out_model                         small
% 2.32/0.99  --sat_out_clauses                       false
% 2.32/0.99  
% 2.32/0.99  ------ QBF Options
% 2.32/0.99  
% 2.32/0.99  --qbf_mode                              false
% 2.32/0.99  --qbf_elim_univ                         false
% 2.32/0.99  --qbf_dom_inst                          none
% 2.32/0.99  --qbf_dom_pre_inst                      false
% 2.32/0.99  --qbf_sk_in                             false
% 2.32/0.99  --qbf_pred_elim                         true
% 2.32/0.99  --qbf_split                             512
% 2.32/0.99  
% 2.32/0.99  ------ BMC1 Options
% 2.32/0.99  
% 2.32/0.99  --bmc1_incremental                      false
% 2.32/0.99  --bmc1_axioms                           reachable_all
% 2.32/0.99  --bmc1_min_bound                        0
% 2.32/0.99  --bmc1_max_bound                        -1
% 2.32/0.99  --bmc1_max_bound_default                -1
% 2.32/0.99  --bmc1_symbol_reachability              true
% 2.32/0.99  --bmc1_property_lemmas                  false
% 2.32/0.99  --bmc1_k_induction                      false
% 2.32/0.99  --bmc1_non_equiv_states                 false
% 2.32/0.99  --bmc1_deadlock                         false
% 2.32/0.99  --bmc1_ucm                              false
% 2.32/0.99  --bmc1_add_unsat_core                   none
% 2.32/0.99  --bmc1_unsat_core_children              false
% 2.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/0.99  --bmc1_out_stat                         full
% 2.32/0.99  --bmc1_ground_init                      false
% 2.32/0.99  --bmc1_pre_inst_next_state              false
% 2.32/0.99  --bmc1_pre_inst_state                   false
% 2.32/0.99  --bmc1_pre_inst_reach_state             false
% 2.32/0.99  --bmc1_out_unsat_core                   false
% 2.32/0.99  --bmc1_aig_witness_out                  false
% 2.32/0.99  --bmc1_verbose                          false
% 2.32/0.99  --bmc1_dump_clauses_tptp                false
% 2.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.32/0.99  --bmc1_dump_file                        -
% 2.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.32/0.99  --bmc1_ucm_extend_mode                  1
% 2.32/0.99  --bmc1_ucm_init_mode                    2
% 2.32/0.99  --bmc1_ucm_cone_mode                    none
% 2.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.32/0.99  --bmc1_ucm_relax_model                  4
% 2.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/0.99  --bmc1_ucm_layered_model                none
% 2.32/0.99  --bmc1_ucm_max_lemma_size               10
% 2.32/0.99  
% 2.32/0.99  ------ AIG Options
% 2.32/0.99  
% 2.32/0.99  --aig_mode                              false
% 2.32/0.99  
% 2.32/0.99  ------ Instantiation Options
% 2.32/0.99  
% 2.32/0.99  --instantiation_flag                    true
% 2.32/0.99  --inst_sos_flag                         false
% 2.32/0.99  --inst_sos_phase                        true
% 2.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel_side                     num_symb
% 2.32/0.99  --inst_solver_per_active                1400
% 2.32/0.99  --inst_solver_calls_frac                1.
% 2.32/0.99  --inst_passive_queue_type               priority_queues
% 2.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/0.99  --inst_passive_queues_freq              [25;2]
% 2.32/0.99  --inst_dismatching                      true
% 2.32/0.99  --inst_eager_unprocessed_to_passive     true
% 2.32/0.99  --inst_prop_sim_given                   true
% 2.32/0.99  --inst_prop_sim_new                     false
% 2.32/0.99  --inst_subs_new                         false
% 2.32/0.99  --inst_eq_res_simp                      false
% 2.32/0.99  --inst_subs_given                       false
% 2.32/0.99  --inst_orphan_elimination               true
% 2.32/0.99  --inst_learning_loop_flag               true
% 2.32/0.99  --inst_learning_start                   3000
% 2.32/0.99  --inst_learning_factor                  2
% 2.32/0.99  --inst_start_prop_sim_after_learn       3
% 2.32/0.99  --inst_sel_renew                        solver
% 2.32/0.99  --inst_lit_activity_flag                true
% 2.32/0.99  --inst_restr_to_given                   false
% 2.32/0.99  --inst_activity_threshold               500
% 2.32/0.99  --inst_out_proof                        true
% 2.32/0.99  
% 2.32/0.99  ------ Resolution Options
% 2.32/0.99  
% 2.32/0.99  --resolution_flag                       true
% 2.32/0.99  --res_lit_sel                           adaptive
% 2.32/0.99  --res_lit_sel_side                      none
% 2.32/0.99  --res_ordering                          kbo
% 2.32/0.99  --res_to_prop_solver                    active
% 2.32/0.99  --res_prop_simpl_new                    false
% 2.32/0.99  --res_prop_simpl_given                  true
% 2.32/0.99  --res_passive_queue_type                priority_queues
% 2.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/0.99  --res_passive_queues_freq               [15;5]
% 2.32/0.99  --res_forward_subs                      full
% 2.32/0.99  --res_backward_subs                     full
% 2.32/0.99  --res_forward_subs_resolution           true
% 2.32/0.99  --res_backward_subs_resolution          true
% 2.32/0.99  --res_orphan_elimination                true
% 2.32/0.99  --res_time_limit                        2.
% 2.32/0.99  --res_out_proof                         true
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Options
% 2.32/0.99  
% 2.32/0.99  --superposition_flag                    true
% 2.32/0.99  --sup_passive_queue_type                priority_queues
% 2.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.32/0.99  --demod_completeness_check              fast
% 2.32/0.99  --demod_use_ground                      true
% 2.32/0.99  --sup_to_prop_solver                    passive
% 2.32/0.99  --sup_prop_simpl_new                    true
% 2.32/0.99  --sup_prop_simpl_given                  true
% 2.32/0.99  --sup_fun_splitting                     false
% 2.32/0.99  --sup_smt_interval                      50000
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Simplification Setup
% 2.32/0.99  
% 2.32/0.99  --sup_indices_passive                   []
% 2.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_full_bw                           [BwDemod]
% 2.32/0.99  --sup_immed_triv                        [TrivRules]
% 2.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_immed_bw_main                     []
% 2.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  
% 2.32/0.99  ------ Combination Options
% 2.32/0.99  
% 2.32/0.99  --comb_res_mult                         3
% 2.32/0.99  --comb_sup_mult                         2
% 2.32/0.99  --comb_inst_mult                        10
% 2.32/0.99  
% 2.32/0.99  ------ Debug Options
% 2.32/0.99  
% 2.32/0.99  --dbg_backtrace                         false
% 2.32/0.99  --dbg_dump_prop_clauses                 false
% 2.32/0.99  --dbg_dump_prop_clauses_file            -
% 2.32/0.99  --dbg_out_stat                          false
% 2.32/0.99  ------ Parsing...
% 2.32/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.32/0.99  ------ Proving...
% 2.32/0.99  ------ Problem Properties 
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  clauses                                 32
% 2.32/0.99  conjectures                             16
% 2.32/0.99  EPR                                     16
% 2.32/0.99  Horn                                    24
% 2.32/0.99  unary                                   15
% 2.32/0.99  binary                                  0
% 2.32/0.99  lits                                    133
% 2.32/0.99  lits eq                                 6
% 2.32/0.99  fd_pure                                 0
% 2.32/0.99  fd_pseudo                               0
% 2.32/0.99  fd_cond                                 3
% 2.32/0.99  fd_pseudo_cond                          0
% 2.32/0.99  AC symbols                              0
% 2.32/0.99  
% 2.32/0.99  ------ Schedule dynamic 5 is on 
% 2.32/0.99  
% 2.32/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  ------ 
% 2.32/0.99  Current options:
% 2.32/0.99  ------ 
% 2.32/0.99  
% 2.32/0.99  ------ Input Options
% 2.32/0.99  
% 2.32/0.99  --out_options                           all
% 2.32/0.99  --tptp_safe_out                         true
% 2.32/0.99  --problem_path                          ""
% 2.32/0.99  --include_path                          ""
% 2.32/0.99  --clausifier                            res/vclausify_rel
% 2.32/0.99  --clausifier_options                    --mode clausify
% 2.32/0.99  --stdin                                 false
% 2.32/0.99  --stats_out                             all
% 2.32/0.99  
% 2.32/0.99  ------ General Options
% 2.32/0.99  
% 2.32/0.99  --fof                                   false
% 2.32/0.99  --time_out_real                         305.
% 2.32/0.99  --time_out_virtual                      -1.
% 2.32/0.99  --symbol_type_check                     false
% 2.32/0.99  --clausify_out                          false
% 2.32/0.99  --sig_cnt_out                           false
% 2.32/0.99  --trig_cnt_out                          false
% 2.32/0.99  --trig_cnt_out_tolerance                1.
% 2.32/0.99  --trig_cnt_out_sk_spl                   false
% 2.32/0.99  --abstr_cl_out                          false
% 2.32/0.99  
% 2.32/0.99  ------ Global Options
% 2.32/0.99  
% 2.32/0.99  --schedule                              default
% 2.32/0.99  --add_important_lit                     false
% 2.32/0.99  --prop_solver_per_cl                    1000
% 2.32/0.99  --min_unsat_core                        false
% 2.32/0.99  --soft_assumptions                      false
% 2.32/0.99  --soft_lemma_size                       3
% 2.32/0.99  --prop_impl_unit_size                   0
% 2.32/0.99  --prop_impl_unit                        []
% 2.32/0.99  --share_sel_clauses                     true
% 2.32/0.99  --reset_solvers                         false
% 2.32/0.99  --bc_imp_inh                            [conj_cone]
% 2.32/0.99  --conj_cone_tolerance                   3.
% 2.32/0.99  --extra_neg_conj                        none
% 2.32/0.99  --large_theory_mode                     true
% 2.32/0.99  --prolific_symb_bound                   200
% 2.32/0.99  --lt_threshold                          2000
% 2.32/0.99  --clause_weak_htbl                      true
% 2.32/0.99  --gc_record_bc_elim                     false
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing Options
% 2.32/0.99  
% 2.32/0.99  --preprocessing_flag                    true
% 2.32/0.99  --time_out_prep_mult                    0.1
% 2.32/0.99  --splitting_mode                        input
% 2.32/0.99  --splitting_grd                         true
% 2.32/0.99  --splitting_cvd                         false
% 2.32/0.99  --splitting_cvd_svl                     false
% 2.32/0.99  --splitting_nvd                         32
% 2.32/0.99  --sub_typing                            true
% 2.32/0.99  --prep_gs_sim                           true
% 2.32/0.99  --prep_unflatten                        true
% 2.32/0.99  --prep_res_sim                          true
% 2.32/0.99  --prep_upred                            true
% 2.32/0.99  --prep_sem_filter                       exhaustive
% 2.32/0.99  --prep_sem_filter_out                   false
% 2.32/0.99  --pred_elim                             true
% 2.32/0.99  --res_sim_input                         true
% 2.32/0.99  --eq_ax_congr_red                       true
% 2.32/0.99  --pure_diseq_elim                       true
% 2.32/0.99  --brand_transform                       false
% 2.32/0.99  --non_eq_to_eq                          false
% 2.32/0.99  --prep_def_merge                        true
% 2.32/0.99  --prep_def_merge_prop_impl              false
% 2.32/0.99  --prep_def_merge_mbd                    true
% 2.32/0.99  --prep_def_merge_tr_red                 false
% 2.32/0.99  --prep_def_merge_tr_cl                  false
% 2.32/0.99  --smt_preprocessing                     true
% 2.32/0.99  --smt_ac_axioms                         fast
% 2.32/0.99  --preprocessed_out                      false
% 2.32/0.99  --preprocessed_stats                    false
% 2.32/0.99  
% 2.32/0.99  ------ Abstraction refinement Options
% 2.32/0.99  
% 2.32/0.99  --abstr_ref                             []
% 2.32/0.99  --abstr_ref_prep                        false
% 2.32/0.99  --abstr_ref_until_sat                   false
% 2.32/0.99  --abstr_ref_sig_restrict                funpre
% 2.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/0.99  --abstr_ref_under                       []
% 2.32/0.99  
% 2.32/0.99  ------ SAT Options
% 2.32/0.99  
% 2.32/0.99  --sat_mode                              false
% 2.32/0.99  --sat_fm_restart_options                ""
% 2.32/0.99  --sat_gr_def                            false
% 2.32/0.99  --sat_epr_types                         true
% 2.32/0.99  --sat_non_cyclic_types                  false
% 2.32/0.99  --sat_finite_models                     false
% 2.32/0.99  --sat_fm_lemmas                         false
% 2.32/0.99  --sat_fm_prep                           false
% 2.32/0.99  --sat_fm_uc_incr                        true
% 2.32/0.99  --sat_out_model                         small
% 2.32/0.99  --sat_out_clauses                       false
% 2.32/0.99  
% 2.32/0.99  ------ QBF Options
% 2.32/0.99  
% 2.32/0.99  --qbf_mode                              false
% 2.32/0.99  --qbf_elim_univ                         false
% 2.32/0.99  --qbf_dom_inst                          none
% 2.32/0.99  --qbf_dom_pre_inst                      false
% 2.32/0.99  --qbf_sk_in                             false
% 2.32/0.99  --qbf_pred_elim                         true
% 2.32/0.99  --qbf_split                             512
% 2.32/0.99  
% 2.32/0.99  ------ BMC1 Options
% 2.32/0.99  
% 2.32/0.99  --bmc1_incremental                      false
% 2.32/0.99  --bmc1_axioms                           reachable_all
% 2.32/0.99  --bmc1_min_bound                        0
% 2.32/0.99  --bmc1_max_bound                        -1
% 2.32/0.99  --bmc1_max_bound_default                -1
% 2.32/0.99  --bmc1_symbol_reachability              true
% 2.32/0.99  --bmc1_property_lemmas                  false
% 2.32/0.99  --bmc1_k_induction                      false
% 2.32/0.99  --bmc1_non_equiv_states                 false
% 2.32/0.99  --bmc1_deadlock                         false
% 2.32/0.99  --bmc1_ucm                              false
% 2.32/0.99  --bmc1_add_unsat_core                   none
% 2.32/0.99  --bmc1_unsat_core_children              false
% 2.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/0.99  --bmc1_out_stat                         full
% 2.32/0.99  --bmc1_ground_init                      false
% 2.32/0.99  --bmc1_pre_inst_next_state              false
% 2.32/0.99  --bmc1_pre_inst_state                   false
% 2.32/0.99  --bmc1_pre_inst_reach_state             false
% 2.32/0.99  --bmc1_out_unsat_core                   false
% 2.32/0.99  --bmc1_aig_witness_out                  false
% 2.32/0.99  --bmc1_verbose                          false
% 2.32/0.99  --bmc1_dump_clauses_tptp                false
% 2.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.32/0.99  --bmc1_dump_file                        -
% 2.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.32/0.99  --bmc1_ucm_extend_mode                  1
% 2.32/0.99  --bmc1_ucm_init_mode                    2
% 2.32/0.99  --bmc1_ucm_cone_mode                    none
% 2.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.32/0.99  --bmc1_ucm_relax_model                  4
% 2.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/0.99  --bmc1_ucm_layered_model                none
% 2.32/0.99  --bmc1_ucm_max_lemma_size               10
% 2.32/0.99  
% 2.32/0.99  ------ AIG Options
% 2.32/0.99  
% 2.32/0.99  --aig_mode                              false
% 2.32/0.99  
% 2.32/0.99  ------ Instantiation Options
% 2.32/0.99  
% 2.32/0.99  --instantiation_flag                    true
% 2.32/0.99  --inst_sos_flag                         false
% 2.32/0.99  --inst_sos_phase                        true
% 2.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel_side                     none
% 2.32/0.99  --inst_solver_per_active                1400
% 2.32/0.99  --inst_solver_calls_frac                1.
% 2.32/0.99  --inst_passive_queue_type               priority_queues
% 2.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/0.99  --inst_passive_queues_freq              [25;2]
% 2.32/0.99  --inst_dismatching                      true
% 2.32/0.99  --inst_eager_unprocessed_to_passive     true
% 2.32/0.99  --inst_prop_sim_given                   true
% 2.32/0.99  --inst_prop_sim_new                     false
% 2.32/0.99  --inst_subs_new                         false
% 2.32/0.99  --inst_eq_res_simp                      false
% 2.32/0.99  --inst_subs_given                       false
% 2.32/0.99  --inst_orphan_elimination               true
% 2.32/0.99  --inst_learning_loop_flag               true
% 2.32/0.99  --inst_learning_start                   3000
% 2.32/0.99  --inst_learning_factor                  2
% 2.32/0.99  --inst_start_prop_sim_after_learn       3
% 2.32/0.99  --inst_sel_renew                        solver
% 2.32/0.99  --inst_lit_activity_flag                true
% 2.32/0.99  --inst_restr_to_given                   false
% 2.32/0.99  --inst_activity_threshold               500
% 2.32/0.99  --inst_out_proof                        true
% 2.32/0.99  
% 2.32/0.99  ------ Resolution Options
% 2.32/0.99  
% 2.32/0.99  --resolution_flag                       false
% 2.32/0.99  --res_lit_sel                           adaptive
% 2.32/0.99  --res_lit_sel_side                      none
% 2.32/0.99  --res_ordering                          kbo
% 2.32/0.99  --res_to_prop_solver                    active
% 2.32/0.99  --res_prop_simpl_new                    false
% 2.32/0.99  --res_prop_simpl_given                  true
% 2.32/0.99  --res_passive_queue_type                priority_queues
% 2.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/0.99  --res_passive_queues_freq               [15;5]
% 2.32/0.99  --res_forward_subs                      full
% 2.32/0.99  --res_backward_subs                     full
% 2.32/0.99  --res_forward_subs_resolution           true
% 2.32/0.99  --res_backward_subs_resolution          true
% 2.32/0.99  --res_orphan_elimination                true
% 2.32/0.99  --res_time_limit                        2.
% 2.32/0.99  --res_out_proof                         true
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Options
% 2.32/0.99  
% 2.32/0.99  --superposition_flag                    true
% 2.32/0.99  --sup_passive_queue_type                priority_queues
% 2.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.32/0.99  --demod_completeness_check              fast
% 2.32/0.99  --demod_use_ground                      true
% 2.32/0.99  --sup_to_prop_solver                    passive
% 2.32/0.99  --sup_prop_simpl_new                    true
% 2.32/0.99  --sup_prop_simpl_given                  true
% 2.32/0.99  --sup_fun_splitting                     false
% 2.32/0.99  --sup_smt_interval                      50000
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Simplification Setup
% 2.32/0.99  
% 2.32/0.99  --sup_indices_passive                   []
% 2.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_full_bw                           [BwDemod]
% 2.32/0.99  --sup_immed_triv                        [TrivRules]
% 2.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_immed_bw_main                     []
% 2.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  
% 2.32/0.99  ------ Combination Options
% 2.32/0.99  
% 2.32/0.99  --comb_res_mult                         3
% 2.32/0.99  --comb_sup_mult                         2
% 2.32/0.99  --comb_inst_mult                        10
% 2.32/0.99  
% 2.32/0.99  ------ Debug Options
% 2.32/0.99  
% 2.32/0.99  --dbg_backtrace                         false
% 2.32/0.99  --dbg_dump_prop_clauses                 false
% 2.32/0.99  --dbg_dump_prop_clauses_file            -
% 2.32/0.99  --dbg_out_stat                          false
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  ------ Proving...
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  % SZS status Theorem for theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  fof(f12,conjecture,(
% 2.32/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)))))))))),
% 2.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f13,negated_conjecture,(
% 2.32/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)))))))))),
% 2.32/0.99    inference(negated_conjecture,[],[f12])).
% 2.32/0.99  
% 2.32/0.99  fof(f31,plain,(
% 2.32/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.32/0.99    inference(ennf_transformation,[],[f13])).
% 2.32/0.99  
% 2.32/0.99  fof(f32,plain,(
% 2.32/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.32/0.99    inference(flattening,[],[f31])).
% 2.32/0.99  
% 2.32/0.99  fof(f37,plain,(
% 2.32/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,sK4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,sK4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,sK4))) & m1_pre_topc(X3,X2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(sK4,X2,X1) & v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f36,plain,(
% 2.32/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,sK3,X4),sK3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,sK3,X4),u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,sK3,X4))) & m1_pre_topc(sK3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f35,plain,(
% 2.32/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,sK2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,sK2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,sK2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,sK2,X3,X4))) & m1_pre_topc(X3,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X4,sK2,X1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f34,plain,(
% 2.32/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,sK1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(X0,sK1,X2,X3,X4),X3,sK1) | ~v1_funct_2(k3_tmap_1(X0,sK1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(X0,sK1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(X4,X2,sK1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f33,plain,(
% 2.32/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f38,plain,(
% 2.32/0.99    (((((~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) & m1_pre_topc(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(sK4,sK2,sK1) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f32,f37,f36,f35,f34,f33])).
% 2.32/1.00  
% 2.32/1.00  fof(f64,plain,(
% 2.32/1.00    m1_pre_topc(sK2,sK0)),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f71,plain,(
% 2.32/1.00    m1_pre_topc(sK3,sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f70,plain,(
% 2.32/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f8,axiom,(
% 2.32/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f24,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f8])).
% 2.32/1.00  
% 2.32/1.00  fof(f25,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f24])).
% 2.32/1.00  
% 2.32/1.00  fof(f51,plain,(
% 2.32/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f25])).
% 2.32/1.00  
% 2.32/1.00  fof(f11,axiom,(
% 2.32/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f29,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f11])).
% 2.32/1.00  
% 2.32/1.00  fof(f30,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.32/1.00    inference(flattening,[],[f29])).
% 2.32/1.00  
% 2.32/1.00  fof(f56,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f30])).
% 2.32/1.00  
% 2.32/1.00  fof(f60,plain,(
% 2.32/1.00    ~v2_struct_0(sK1)),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f61,plain,(
% 2.32/1.00    v2_pre_topc(sK1)),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f62,plain,(
% 2.32/1.00    l1_pre_topc(sK1)),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f67,plain,(
% 2.32/1.00    v1_funct_1(sK4)),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f68,plain,(
% 2.32/1.00    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f7,axiom,(
% 2.32/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f22,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f7])).
% 2.32/1.00  
% 2.32/1.00  fof(f23,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f22])).
% 2.32/1.00  
% 2.32/1.00  fof(f50,plain,(
% 2.32/1.00    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f23])).
% 2.32/1.00  
% 2.32/1.00  fof(f58,plain,(
% 2.32/1.00    v2_pre_topc(sK0)),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f59,plain,(
% 2.32/1.00    l1_pre_topc(sK0)),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f63,plain,(
% 2.32/1.00    ~v2_struct_0(sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f5,axiom,(
% 2.32/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f19,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f5])).
% 2.32/1.00  
% 2.32/1.00  fof(f48,plain,(
% 2.32/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f19])).
% 2.32/1.00  
% 2.32/1.00  fof(f3,axiom,(
% 2.32/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f16,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f3])).
% 2.32/1.00  
% 2.32/1.00  fof(f17,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.32/1.00    inference(flattening,[],[f16])).
% 2.32/1.00  
% 2.32/1.00  fof(f46,plain,(
% 2.32/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f17])).
% 2.32/1.00  
% 2.32/1.00  fof(f57,plain,(
% 2.32/1.00    ~v2_struct_0(sK0)),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f72,plain,(
% 2.32/1.00    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f2,axiom,(
% 2.32/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f14,plain,(
% 2.32/1.00    ! [X0,X1,X2,X3] : ((((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.32/1.00    inference(ennf_transformation,[],[f2])).
% 2.32/1.00  
% 2.32/1.00  fof(f15,plain,(
% 2.32/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.32/1.00    inference(flattening,[],[f14])).
% 2.32/1.00  
% 2.32/1.00  fof(f44,plain,(
% 2.32/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | k1_xboole_0 = X1 | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f15])).
% 2.32/1.00  
% 2.32/1.00  fof(f9,axiom,(
% 2.32/1.00    ! [X0,X1,X2,X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f26,plain,(
% 2.32/1.00    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f9])).
% 2.32/1.00  
% 2.32/1.00  fof(f27,plain,(
% 2.32/1.00    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f26])).
% 2.32/1.00  
% 2.32/1.00  fof(f54,plain,(
% 2.32/1.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f27])).
% 2.32/1.00  
% 2.32/1.00  fof(f53,plain,(
% 2.32/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f27])).
% 2.32/1.00  
% 2.32/1.00  fof(f52,plain,(
% 2.32/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f27])).
% 2.32/1.00  
% 2.32/1.00  fof(f10,axiom,(
% 2.32/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f28,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f10])).
% 2.32/1.00  
% 2.32/1.00  fof(f55,plain,(
% 2.32/1.00    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f28])).
% 2.32/1.00  
% 2.32/1.00  fof(f4,axiom,(
% 2.32/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f18,plain,(
% 2.32/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f4])).
% 2.32/1.00  
% 2.32/1.00  fof(f47,plain,(
% 2.32/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f18])).
% 2.32/1.00  
% 2.32/1.00  fof(f1,axiom,(
% 2.32/1.00    v1_xboole_0(k1_xboole_0)),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f39,plain,(
% 2.32/1.00    v1_xboole_0(k1_xboole_0)),
% 2.32/1.00    inference(cnf_transformation,[],[f1])).
% 2.32/1.00  
% 2.32/1.00  fof(f6,axiom,(
% 2.32/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f20,plain,(
% 2.32/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f6])).
% 2.32/1.00  
% 2.32/1.00  fof(f21,plain,(
% 2.32/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f20])).
% 2.32/1.00  
% 2.32/1.00  fof(f49,plain,(
% 2.32/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f21])).
% 2.32/1.00  
% 2.32/1.00  fof(f69,plain,(
% 2.32/1.00    v5_pre_topc(sK4,sK2,sK1)),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f65,plain,(
% 2.32/1.00    ~v2_struct_0(sK3)),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  cnf(c_26,negated_conjecture,
% 2.32/1.00      ( m1_pre_topc(sK2,sK0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1002,negated_conjecture,
% 2.32/1.00      ( m1_pre_topc(sK2,sK0) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_26]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1612,plain,
% 2.32/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1002]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_19,negated_conjecture,
% 2.32/1.00      ( m1_pre_topc(sK3,sK2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1009,negated_conjecture,
% 2.32/1.00      ( m1_pre_topc(sK3,sK2) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1605,plain,
% 2.32/1.00      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1009]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_20,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 2.32/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1008,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1606,plain,
% 2.32/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1008]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_12,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.32/1.00      | ~ m1_pre_topc(X3,X4)
% 2.32/1.00      | ~ m1_pre_topc(X3,X1)
% 2.32/1.00      | ~ m1_pre_topc(X1,X4)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.32/1.00      | v2_struct_0(X4)
% 2.32/1.00      | v2_struct_0(X2)
% 2.32/1.00      | ~ l1_pre_topc(X4)
% 2.32/1.00      | ~ l1_pre_topc(X2)
% 2.32/1.00      | ~ v2_pre_topc(X4)
% 2.32/1.00      | ~ v2_pre_topc(X2)
% 2.32/1.00      | ~ v1_funct_1(X0)
% 2.32/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1016,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 2.32/1.00      | ~ m1_pre_topc(X2_51,X0_51)
% 2.32/1.00      | ~ m1_pre_topc(X2_51,X3_51)
% 2.32/1.00      | ~ m1_pre_topc(X0_51,X3_51)
% 2.32/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 2.32/1.00      | v2_struct_0(X1_51)
% 2.32/1.00      | v2_struct_0(X3_51)
% 2.32/1.00      | ~ l1_pre_topc(X1_51)
% 2.32/1.00      | ~ l1_pre_topc(X3_51)
% 2.32/1.00      | ~ v2_pre_topc(X1_51)
% 2.32/1.00      | ~ v2_pre_topc(X3_51)
% 2.32/1.00      | ~ v1_funct_1(X0_53)
% 2.32/1.00      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_53,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_53) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1598,plain,
% 2.32/1.00      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_53,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_53)
% 2.32/1.00      | v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 2.32/1.00      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 2.32/1.00      | m1_pre_topc(X2_51,X3_51) != iProver_top
% 2.32/1.00      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 2.32/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 2.32/1.00      | v2_struct_0(X1_51) = iProver_top
% 2.32/1.00      | v2_struct_0(X3_51) = iProver_top
% 2.32/1.00      | l1_pre_topc(X1_51) != iProver_top
% 2.32/1.00      | l1_pre_topc(X3_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(X1_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(X3_51) != iProver_top
% 2.32/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1016]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_17,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.32/1.00      | ~ m1_pre_topc(X2,X0)
% 2.32/1.00      | m1_pre_topc(X2,X1)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ v2_pre_topc(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1011,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.32/1.00      | ~ m1_pre_topc(X2_51,X0_51)
% 2.32/1.00      | m1_pre_topc(X2_51,X1_51)
% 2.32/1.00      | ~ l1_pre_topc(X1_51)
% 2.32/1.00      | ~ v2_pre_topc(X1_51) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1603,plain,
% 2.32/1.00      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 2.32/1.00      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 2.32/1.00      | m1_pre_topc(X2_51,X1_51) = iProver_top
% 2.32/1.00      | l1_pre_topc(X1_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(X1_51) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1011]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1874,plain,
% 2.32/1.00      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_53,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_53)
% 2.32/1.00      | v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 2.32/1.00      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 2.32/1.00      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 2.32/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 2.32/1.00      | v2_struct_0(X1_51) = iProver_top
% 2.32/1.00      | v2_struct_0(X3_51) = iProver_top
% 2.32/1.00      | l1_pre_topc(X1_51) != iProver_top
% 2.32/1.00      | l1_pre_topc(X3_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(X1_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(X3_51) != iProver_top
% 2.32/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.32/1.00      inference(forward_subsumption_resolution,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_1598,c_1603]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4124,plain,
% 2.32/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK4)
% 2.32/1.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.32/1.00      | m1_pre_topc(X0_51,sK2) != iProver_top
% 2.32/1.00      | m1_pre_topc(sK2,X1_51) != iProver_top
% 2.32/1.00      | v2_struct_0(X1_51) = iProver_top
% 2.32/1.00      | v2_struct_0(sK1) = iProver_top
% 2.32/1.00      | l1_pre_topc(X1_51) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.32/1.00      | v2_pre_topc(X1_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1606,c_1874]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_30,negated_conjecture,
% 2.32/1.00      ( ~ v2_struct_0(sK1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_37,plain,
% 2.32/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_29,negated_conjecture,
% 2.32/1.00      ( v2_pre_topc(sK1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_38,plain,
% 2.32/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_28,negated_conjecture,
% 2.32/1.00      ( l1_pre_topc(sK1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_39,plain,
% 2.32/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_23,negated_conjecture,
% 2.32/1.00      ( v1_funct_1(sK4) ),
% 2.32/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_44,plain,
% 2.32/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_22,negated_conjecture,
% 2.32/1.00      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_45,plain,
% 2.32/1.00      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4247,plain,
% 2.32/1.00      ( l1_pre_topc(X1_51) != iProver_top
% 2.32/1.00      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK4)
% 2.32/1.00      | m1_pre_topc(X0_51,sK2) != iProver_top
% 2.32/1.00      | m1_pre_topc(sK2,X1_51) != iProver_top
% 2.32/1.00      | v2_struct_0(X1_51) = iProver_top
% 2.32/1.00      | v2_pre_topc(X1_51) != iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_4124,c_37,c_38,c_39,c_44,c_45]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4248,plain,
% 2.32/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK4)
% 2.32/1.00      | m1_pre_topc(X0_51,sK2) != iProver_top
% 2.32/1.00      | m1_pre_topc(sK2,X1_51) != iProver_top
% 2.32/1.00      | v2_struct_0(X1_51) = iProver_top
% 2.32/1.00      | l1_pre_topc(X1_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(X1_51) != iProver_top ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_4247]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4259,plain,
% 2.32/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0_51,sK1,sK2,sK3,sK4)
% 2.32/1.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 2.32/1.00      | v2_struct_0(X0_51) = iProver_top
% 2.32/1.00      | l1_pre_topc(X0_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(X0_51) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1605,c_4248]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_11,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.32/1.00      | ~ m1_pre_topc(X3,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | v2_struct_0(X2)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ l1_pre_topc(X2)
% 2.32/1.00      | ~ v2_pre_topc(X1)
% 2.32/1.00      | ~ v2_pre_topc(X2)
% 2.32/1.00      | ~ v1_funct_1(X0)
% 2.32/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.32/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1017,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 2.32/1.00      | ~ m1_pre_topc(X2_51,X0_51)
% 2.32/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 2.32/1.00      | v2_struct_0(X0_51)
% 2.32/1.00      | v2_struct_0(X1_51)
% 2.32/1.00      | ~ l1_pre_topc(X0_51)
% 2.32/1.00      | ~ l1_pre_topc(X1_51)
% 2.32/1.00      | ~ v2_pre_topc(X1_51)
% 2.32/1.00      | ~ v2_pre_topc(X0_51)
% 2.32/1.00      | ~ v1_funct_1(X0_53)
% 2.32/1.00      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_53,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_53,X2_51) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1597,plain,
% 2.32/1.00      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_53,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_53,X2_51)
% 2.32/1.00      | v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 2.32/1.00      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 2.32/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 2.32/1.00      | v2_struct_0(X1_51) = iProver_top
% 2.32/1.00      | v2_struct_0(X0_51) = iProver_top
% 2.32/1.00      | l1_pre_topc(X1_51) != iProver_top
% 2.32/1.00      | l1_pre_topc(X0_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(X1_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(X0_51) != iProver_top
% 2.32/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1017]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2989,plain,
% 2.32/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK4,X0_51)
% 2.32/1.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.32/1.00      | m1_pre_topc(X0_51,sK2) != iProver_top
% 2.32/1.00      | v2_struct_0(sK2) = iProver_top
% 2.32/1.00      | v2_struct_0(sK1) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.32/1.00      | v2_pre_topc(sK2) != iProver_top
% 2.32/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1606,c_1597]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_32,negated_conjecture,
% 2.32/1.00      ( v2_pre_topc(sK0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_35,plain,
% 2.32/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_31,negated_conjecture,
% 2.32/1.00      ( l1_pre_topc(sK0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_36,plain,
% 2.32/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_27,negated_conjecture,
% 2.32/1.00      ( ~ v2_struct_0(sK2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_40,plain,
% 2.32/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_41,plain,
% 2.32/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_9,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1018,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.32/1.00      | ~ l1_pre_topc(X1_51)
% 2.32/1.00      | l1_pre_topc(X0_51) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2120,plain,
% 2.32/1.00      ( ~ m1_pre_topc(sK2,X0_51)
% 2.32/1.00      | ~ l1_pre_topc(X0_51)
% 2.32/1.00      | l1_pre_topc(sK2) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1018]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2231,plain,
% 2.32/1.00      ( ~ m1_pre_topc(sK2,sK0) | l1_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2120]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2232,plain,
% 2.32/1.00      ( m1_pre_topc(sK2,sK0) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2231]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_7,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ v2_pre_topc(X1)
% 2.32/1.00      | v2_pre_topc(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1019,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.32/1.00      | ~ l1_pre_topc(X1_51)
% 2.32/1.00      | ~ v2_pre_topc(X1_51)
% 2.32/1.00      | v2_pre_topc(X0_51) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1595,plain,
% 2.32/1.00      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 2.32/1.00      | l1_pre_topc(X1_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(X1_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(X0_51) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1019]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2463,plain,
% 2.32/1.00      ( l1_pre_topc(sK0) != iProver_top
% 2.32/1.00      | v2_pre_topc(sK2) = iProver_top
% 2.32/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1612,c_1595]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3490,plain,
% 2.32/1.00      ( m1_pre_topc(X0_51,sK2) != iProver_top
% 2.32/1.00      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK4,X0_51) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_2989,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_44,c_45,
% 2.32/1.00                 c_2232,c_2463]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3491,plain,
% 2.32/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK4,X0_51)
% 2.32/1.00      | m1_pre_topc(X0_51,sK2) != iProver_top ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_3490]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3498,plain,
% 2.32/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK4,sK3) ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1605,c_3491]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4260,plain,
% 2.32/1.00      ( k3_tmap_1(X0_51,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
% 2.32/1.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 2.32/1.00      | v2_struct_0(X0_51) = iProver_top
% 2.32/1.00      | l1_pre_topc(X0_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(X0_51) != iProver_top ),
% 2.32/1.00      inference(light_normalisation,[status(thm)],[c_4259,c_3498]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4364,plain,
% 2.32/1.00      ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
% 2.32/1.00      | v2_struct_0(sK0) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.32/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1612,c_4260]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_33,negated_conjecture,
% 2.32/1.00      ( ~ v2_struct_0(sK0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_34,plain,
% 2.32/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4367,plain,
% 2.32/1.00      ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_4364,c_34,c_35,c_36]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_18,negated_conjecture,
% 2.32/1.00      ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
% 2.32/1.00      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
% 2.32/1.00      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.32/1.00      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1010,negated_conjecture,
% 2.32/1.00      ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
% 2.32/1.00      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
% 2.32/1.00      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.32/1.00      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1604,plain,
% 2.32/1.00      ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) != iProver_top
% 2.32/1.00      | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.32/1.00      | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.32/1.00      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1010]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4370,plain,
% 2.32/1.00      ( v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) != iProver_top
% 2.32/1.00      | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.32/1.00      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.32/1.00      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
% 2.32/1.00      inference(demodulation,[status(thm)],[c_4367,c_1604]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.32/1.00      | ~ r1_tarski(X3,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 2.32/1.00      | ~ v1_funct_1(X0)
% 2.32/1.00      | k1_xboole_0 = X2 ),
% 2.32/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1024,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0_53,X0_52,X1_52)
% 2.32/1.00      | ~ r1_tarski(X2_52,X0_52)
% 2.32/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.32/1.00      | m1_subset_1(k2_partfun1(X0_52,X1_52,X0_53,X2_52),k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52)))
% 2.32/1.00      | ~ v1_funct_1(X0_53)
% 2.32/1.00      | k1_xboole_0 = X1_52 ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1590,plain,
% 2.32/1.00      ( k1_xboole_0 = X0_52
% 2.32/1.00      | v1_funct_2(X0_53,X1_52,X0_52) != iProver_top
% 2.32/1.00      | r1_tarski(X2_52,X1_52) != iProver_top
% 2.32/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) != iProver_top
% 2.32/1.00      | m1_subset_1(k2_partfun1(X1_52,X0_52,X0_53,X2_52),k1_zfmisc_1(k2_zfmisc_1(X2_52,X0_52))) = iProver_top
% 2.32/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1024]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3501,plain,
% 2.32/1.00      ( u1_struct_0(sK1) = k1_xboole_0
% 2.32/1.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.32/1.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 2.32/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_3498,c_1590]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_13,plain,
% 2.32/1.00      ( ~ v5_pre_topc(X0,X1,X2)
% 2.32/1.00      | v5_pre_topc(k2_tmap_1(X1,X2,X0,X3),X3,X2)
% 2.32/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.32/1.00      | ~ m1_pre_topc(X3,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | v2_struct_0(X2)
% 2.32/1.00      | v2_struct_0(X3)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ l1_pre_topc(X2)
% 2.32/1.00      | ~ v2_pre_topc(X1)
% 2.32/1.00      | ~ v2_pre_topc(X2)
% 2.32/1.00      | ~ v1_funct_1(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1015,plain,
% 2.32/1.00      ( ~ v5_pre_topc(X0_53,X0_51,X1_51)
% 2.32/1.00      | v5_pre_topc(k2_tmap_1(X0_51,X1_51,X0_53,X2_51),X2_51,X1_51)
% 2.32/1.00      | ~ v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 2.32/1.00      | ~ m1_pre_topc(X2_51,X0_51)
% 2.32/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 2.32/1.00      | v2_struct_0(X0_51)
% 2.32/1.00      | v2_struct_0(X1_51)
% 2.32/1.00      | v2_struct_0(X2_51)
% 2.32/1.00      | ~ l1_pre_topc(X0_51)
% 2.32/1.00      | ~ l1_pre_topc(X1_51)
% 2.32/1.00      | ~ v2_pre_topc(X1_51)
% 2.32/1.00      | ~ v2_pre_topc(X0_51)
% 2.32/1.00      | ~ v1_funct_1(X0_53) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2055,plain,
% 2.32/1.00      ( ~ v5_pre_topc(X0_53,sK2,X0_51)
% 2.32/1.00      | v5_pre_topc(k2_tmap_1(sK2,X0_51,X0_53,sK3),sK3,X0_51)
% 2.32/1.00      | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_51))
% 2.32/1.00      | ~ m1_pre_topc(sK3,sK2)
% 2.32/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_51))))
% 2.32/1.00      | v2_struct_0(X0_51)
% 2.32/1.00      | v2_struct_0(sK3)
% 2.32/1.00      | v2_struct_0(sK2)
% 2.32/1.00      | ~ l1_pre_topc(X0_51)
% 2.32/1.00      | ~ l1_pre_topc(sK2)
% 2.32/1.00      | ~ v2_pre_topc(X0_51)
% 2.32/1.00      | ~ v2_pre_topc(sK2)
% 2.32/1.00      | ~ v1_funct_1(X0_53) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1015]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2056,plain,
% 2.32/1.00      ( v5_pre_topc(X0_53,sK2,X0_51) != iProver_top
% 2.32/1.00      | v5_pre_topc(k2_tmap_1(sK2,X0_51,X0_53,sK3),sK3,X0_51) = iProver_top
% 2.32/1.00      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_51)) != iProver_top
% 2.32/1.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.32/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_51)))) != iProver_top
% 2.32/1.00      | v2_struct_0(X0_51) = iProver_top
% 2.32/1.00      | v2_struct_0(sK3) = iProver_top
% 2.32/1.00      | v2_struct_0(sK2) = iProver_top
% 2.32/1.00      | l1_pre_topc(X0_51) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | v2_pre_topc(X0_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(sK2) != iProver_top
% 2.32/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2055]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2058,plain,
% 2.32/1.00      ( v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) = iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,sK2,sK1) != iProver_top
% 2.32/1.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.32/1.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.32/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.32/1.00      | v2_struct_0(sK3) = iProver_top
% 2.32/1.00      | v2_struct_0(sK2) = iProver_top
% 2.32/1.00      | v2_struct_0(sK1) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.32/1.00      | v2_pre_topc(sK2) != iProver_top
% 2.32/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2056]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_14,plain,
% 2.32/1.00      ( ~ v5_pre_topc(X0,X1,X2)
% 2.32/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.32/1.00      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 2.32/1.00      | ~ m1_pre_topc(X3,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | v2_struct_0(X2)
% 2.32/1.00      | v2_struct_0(X3)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ l1_pre_topc(X2)
% 2.32/1.00      | ~ v2_pre_topc(X1)
% 2.32/1.00      | ~ v2_pre_topc(X2)
% 2.32/1.00      | ~ v1_funct_1(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1014,plain,
% 2.32/1.00      ( ~ v5_pre_topc(X0_53,X0_51,X1_51)
% 2.32/1.00      | ~ v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 2.32/1.00      | v1_funct_2(k2_tmap_1(X0_51,X1_51,X0_53,X2_51),u1_struct_0(X2_51),u1_struct_0(X1_51))
% 2.32/1.00      | ~ m1_pre_topc(X2_51,X0_51)
% 2.32/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 2.32/1.00      | v2_struct_0(X0_51)
% 2.32/1.00      | v2_struct_0(X1_51)
% 2.32/1.00      | v2_struct_0(X2_51)
% 2.32/1.00      | ~ l1_pre_topc(X0_51)
% 2.32/1.00      | ~ l1_pre_topc(X1_51)
% 2.32/1.00      | ~ v2_pre_topc(X1_51)
% 2.32/1.00      | ~ v2_pre_topc(X0_51)
% 2.32/1.00      | ~ v1_funct_1(X0_53) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2040,plain,
% 2.32/1.00      ( ~ v5_pre_topc(X0_53,sK2,X0_51)
% 2.32/1.00      | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_51))
% 2.32/1.00      | v1_funct_2(k2_tmap_1(sK2,X0_51,X0_53,sK3),u1_struct_0(sK3),u1_struct_0(X0_51))
% 2.32/1.00      | ~ m1_pre_topc(sK3,sK2)
% 2.32/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_51))))
% 2.32/1.00      | v2_struct_0(X0_51)
% 2.32/1.00      | v2_struct_0(sK3)
% 2.32/1.00      | v2_struct_0(sK2)
% 2.32/1.00      | ~ l1_pre_topc(X0_51)
% 2.32/1.00      | ~ l1_pre_topc(sK2)
% 2.32/1.00      | ~ v2_pre_topc(X0_51)
% 2.32/1.00      | ~ v2_pre_topc(sK2)
% 2.32/1.00      | ~ v1_funct_1(X0_53) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1014]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2041,plain,
% 2.32/1.00      ( v5_pre_topc(X0_53,sK2,X0_51) != iProver_top
% 2.32/1.00      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_51)) != iProver_top
% 2.32/1.00      | v1_funct_2(k2_tmap_1(sK2,X0_51,X0_53,sK3),u1_struct_0(sK3),u1_struct_0(X0_51)) = iProver_top
% 2.32/1.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.32/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_51)))) != iProver_top
% 2.32/1.00      | v2_struct_0(X0_51) = iProver_top
% 2.32/1.00      | v2_struct_0(sK3) = iProver_top
% 2.32/1.00      | v2_struct_0(sK2) = iProver_top
% 2.32/1.00      | l1_pre_topc(X0_51) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | v2_pre_topc(X0_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(sK2) != iProver_top
% 2.32/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2040]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2043,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,sK2,sK1) != iProver_top
% 2.32/1.00      | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 2.32/1.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.32/1.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.32/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.32/1.00      | v2_struct_0(sK3) = iProver_top
% 2.32/1.00      | v2_struct_0(sK2) = iProver_top
% 2.32/1.00      | v2_struct_0(sK1) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.32/1.00      | v2_pre_topc(sK2) != iProver_top
% 2.32/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2041]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_15,plain,
% 2.32/1.00      ( ~ v5_pre_topc(X0,X1,X2)
% 2.32/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.32/1.00      | ~ m1_pre_topc(X3,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | v2_struct_0(X2)
% 2.32/1.00      | v2_struct_0(X3)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ l1_pre_topc(X2)
% 2.32/1.00      | ~ v2_pre_topc(X1)
% 2.32/1.00      | ~ v2_pre_topc(X2)
% 2.32/1.00      | ~ v1_funct_1(X0)
% 2.32/1.00      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1013,plain,
% 2.32/1.00      ( ~ v5_pre_topc(X0_53,X0_51,X1_51)
% 2.32/1.00      | ~ v1_funct_2(X0_53,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 2.32/1.00      | ~ m1_pre_topc(X2_51,X0_51)
% 2.32/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 2.32/1.00      | v2_struct_0(X0_51)
% 2.32/1.00      | v2_struct_0(X1_51)
% 2.32/1.00      | v2_struct_0(X2_51)
% 2.32/1.00      | ~ l1_pre_topc(X0_51)
% 2.32/1.00      | ~ l1_pre_topc(X1_51)
% 2.32/1.00      | ~ v2_pre_topc(X1_51)
% 2.32/1.00      | ~ v2_pre_topc(X0_51)
% 2.32/1.00      | ~ v1_funct_1(X0_53)
% 2.32/1.00      | v1_funct_1(k2_tmap_1(X0_51,X1_51,X0_53,X2_51)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2010,plain,
% 2.32/1.00      ( ~ v5_pre_topc(X0_53,sK2,X0_51)
% 2.32/1.00      | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_51))
% 2.32/1.00      | ~ m1_pre_topc(sK3,sK2)
% 2.32/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_51))))
% 2.32/1.00      | v2_struct_0(X0_51)
% 2.32/1.00      | v2_struct_0(sK3)
% 2.32/1.00      | v2_struct_0(sK2)
% 2.32/1.00      | ~ l1_pre_topc(X0_51)
% 2.32/1.00      | ~ l1_pre_topc(sK2)
% 2.32/1.00      | ~ v2_pre_topc(X0_51)
% 2.32/1.00      | ~ v2_pre_topc(sK2)
% 2.32/1.00      | ~ v1_funct_1(X0_53)
% 2.32/1.00      | v1_funct_1(k2_tmap_1(sK2,X0_51,X0_53,sK3)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1013]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2011,plain,
% 2.32/1.00      ( v5_pre_topc(X0_53,sK2,X0_51) != iProver_top
% 2.32/1.00      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_51)) != iProver_top
% 2.32/1.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.32/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_51)))) != iProver_top
% 2.32/1.00      | v2_struct_0(X0_51) = iProver_top
% 2.32/1.00      | v2_struct_0(sK3) = iProver_top
% 2.32/1.00      | v2_struct_0(sK2) = iProver_top
% 2.32/1.00      | l1_pre_topc(X0_51) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | v2_pre_topc(X0_51) != iProver_top
% 2.32/1.00      | v2_pre_topc(sK2) != iProver_top
% 2.32/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.32/1.00      | v1_funct_1(k2_tmap_1(sK2,X0_51,X0_53,sK3)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2010]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2013,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,sK2,sK1) != iProver_top
% 2.32/1.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.32/1.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.32/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.32/1.00      | v2_struct_0(sK3) = iProver_top
% 2.32/1.00      | v2_struct_0(sK2) = iProver_top
% 2.32/1.00      | v2_struct_0(sK1) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.32/1.00      | v2_pre_topc(sK2) != iProver_top
% 2.32/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.32/1.00      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) = iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2011]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_16,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.32/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.32/1.00      | ~ l1_pre_topc(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1012,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.32/1.00      | r1_tarski(u1_struct_0(X0_51),u1_struct_0(X1_51))
% 2.32/1.00      | ~ l1_pre_topc(X1_51) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1969,plain,
% 2.32/1.00      ( ~ m1_pre_topc(sK3,sK2)
% 2.32/1.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
% 2.32/1.00      | ~ l1_pre_topc(sK2) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1012]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1970,plain,
% 2.32/1.00      ( m1_pre_topc(sK3,sK2) != iProver_top
% 2.32/1.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1969]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_8,plain,
% 2.32/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_0,plain,
% 2.32/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_10,plain,
% 2.32/1.00      ( v2_struct_0(X0)
% 2.32/1.00      | ~ l1_struct_0(X0)
% 2.32/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_353,plain,
% 2.32/1.00      ( v2_struct_0(X0)
% 2.32/1.00      | ~ l1_struct_0(X0)
% 2.32/1.00      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_371,plain,
% 2.32/1.00      ( v2_struct_0(X0)
% 2.32/1.00      | ~ l1_pre_topc(X0)
% 2.32/1.00      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.32/1.00      inference(resolution,[status(thm)],[c_8,c_353]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_994,plain,
% 2.32/1.00      ( v2_struct_0(X0_51)
% 2.32/1.00      | ~ l1_pre_topc(X0_51)
% 2.32/1.00      | u1_struct_0(X0_51) != k1_xboole_0 ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_371]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1106,plain,
% 2.32/1.00      ( v2_struct_0(sK1)
% 2.32/1.00      | ~ l1_pre_topc(sK1)
% 2.32/1.00      | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_994]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_48,plain,
% 2.32/1.00      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_47,plain,
% 2.32/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_21,negated_conjecture,
% 2.32/1.00      ( v5_pre_topc(sK4,sK2,sK1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_46,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,sK2,sK1) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_25,negated_conjecture,
% 2.32/1.00      ( ~ v2_struct_0(sK3) ),
% 2.32/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_42,plain,
% 2.32/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(contradiction,plain,
% 2.32/1.00      ( $false ),
% 2.32/1.00      inference(minisat,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_4370,c_3501,c_2463,c_2232,c_2058,c_2043,c_2013,c_1970,
% 2.32/1.00                 c_1106,c_48,c_47,c_46,c_45,c_44,c_42,c_41,c_40,c_39,
% 2.32/1.00                 c_28,c_38,c_37,c_30,c_36,c_35]) ).
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  ------                               Statistics
% 2.32/1.00  
% 2.32/1.00  ------ General
% 2.32/1.00  
% 2.32/1.00  abstr_ref_over_cycles:                  0
% 2.32/1.00  abstr_ref_under_cycles:                 0
% 2.32/1.00  gc_basic_clause_elim:                   0
% 2.32/1.00  forced_gc_time:                         0
% 2.32/1.00  parsing_time:                           0.012
% 2.32/1.00  unif_index_cands_time:                  0.
% 2.32/1.00  unif_index_add_time:                    0.
% 2.32/1.00  orderings_time:                         0.
% 2.32/1.00  out_proof_time:                         0.017
% 2.32/1.00  total_time:                             0.217
% 2.32/1.00  num_of_symbols:                         56
% 2.32/1.00  num_of_terms:                           3382
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing
% 2.32/1.00  
% 2.32/1.00  num_of_splits:                          0
% 2.32/1.00  num_of_split_atoms:                     0
% 2.32/1.00  num_of_reused_defs:                     0
% 2.32/1.00  num_eq_ax_congr_red:                    28
% 2.32/1.00  num_of_sem_filtered_clauses:            1
% 2.32/1.00  num_of_subtypes:                        5
% 2.32/1.00  monotx_restored_types:                  1
% 2.32/1.00  sat_num_of_epr_types:                   0
% 2.32/1.00  sat_num_of_non_cyclic_types:            0
% 2.32/1.00  sat_guarded_non_collapsed_types:        0
% 2.32/1.00  num_pure_diseq_elim:                    0
% 2.32/1.00  simp_replaced_by:                       0
% 2.32/1.00  res_preprocessed:                       161
% 2.32/1.00  prep_upred:                             0
% 2.32/1.00  prep_unflattend:                        18
% 2.32/1.00  smt_new_axioms:                         0
% 2.32/1.00  pred_elim_cands:                        9
% 2.32/1.00  pred_elim:                              2
% 2.32/1.00  pred_elim_cl:                           2
% 2.32/1.00  pred_elim_cycles:                       4
% 2.32/1.00  merged_defs:                            0
% 2.32/1.00  merged_defs_ncl:                        0
% 2.32/1.00  bin_hyper_res:                          0
% 2.32/1.00  prep_cycles:                            4
% 2.32/1.00  pred_elim_time:                         0.01
% 2.32/1.00  splitting_time:                         0.
% 2.32/1.00  sem_filter_time:                        0.
% 2.32/1.00  monotx_time:                            0.001
% 2.32/1.00  subtype_inf_time:                       0.002
% 2.32/1.00  
% 2.32/1.00  ------ Problem properties
% 2.32/1.00  
% 2.32/1.00  clauses:                                32
% 2.32/1.00  conjectures:                            16
% 2.32/1.00  epr:                                    16
% 2.32/1.00  horn:                                   24
% 2.32/1.00  ground:                                 16
% 2.32/1.00  unary:                                  15
% 2.32/1.00  binary:                                 0
% 2.32/1.00  lits:                                   133
% 2.32/1.00  lits_eq:                                6
% 2.32/1.00  fd_pure:                                0
% 2.32/1.00  fd_pseudo:                              0
% 2.32/1.00  fd_cond:                                3
% 2.32/1.00  fd_pseudo_cond:                         0
% 2.32/1.00  ac_symbols:                             0
% 2.32/1.00  
% 2.32/1.00  ------ Propositional Solver
% 2.32/1.00  
% 2.32/1.00  prop_solver_calls:                      27
% 2.32/1.00  prop_fast_solver_calls:                 1670
% 2.32/1.00  smt_solver_calls:                       0
% 2.32/1.00  smt_fast_solver_calls:                  0
% 2.32/1.00  prop_num_of_clauses:                    1099
% 2.32/1.00  prop_preprocess_simplified:             4783
% 2.32/1.00  prop_fo_subsumed:                       92
% 2.32/1.00  prop_solver_time:                       0.
% 2.32/1.00  smt_solver_time:                        0.
% 2.32/1.00  smt_fast_solver_time:                   0.
% 2.32/1.00  prop_fast_solver_time:                  0.
% 2.32/1.00  prop_unsat_core_time:                   0.
% 2.32/1.00  
% 2.32/1.00  ------ QBF
% 2.32/1.00  
% 2.32/1.00  qbf_q_res:                              0
% 2.32/1.00  qbf_num_tautologies:                    0
% 2.32/1.00  qbf_prep_cycles:                        0
% 2.32/1.00  
% 2.32/1.00  ------ BMC1
% 2.32/1.00  
% 2.32/1.00  bmc1_current_bound:                     -1
% 2.32/1.00  bmc1_last_solved_bound:                 -1
% 2.32/1.00  bmc1_unsat_core_size:                   -1
% 2.32/1.00  bmc1_unsat_core_parents_size:           -1
% 2.32/1.00  bmc1_merge_next_fun:                    0
% 2.32/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation
% 2.32/1.00  
% 2.32/1.00  inst_num_of_clauses:                    307
% 2.32/1.00  inst_num_in_passive:                    5
% 2.32/1.00  inst_num_in_active:                     249
% 2.32/1.00  inst_num_in_unprocessed:                53
% 2.32/1.00  inst_num_of_loops:                      280
% 2.32/1.00  inst_num_of_learning_restarts:          0
% 2.32/1.00  inst_num_moves_active_passive:          27
% 2.32/1.00  inst_lit_activity:                      0
% 2.32/1.00  inst_lit_activity_moves:                0
% 2.32/1.00  inst_num_tautologies:                   0
% 2.32/1.00  inst_num_prop_implied:                  0
% 2.32/1.00  inst_num_existing_simplified:           0
% 2.32/1.00  inst_num_eq_res_simplified:             0
% 2.32/1.00  inst_num_child_elim:                    0
% 2.32/1.00  inst_num_of_dismatching_blockings:      13
% 2.32/1.00  inst_num_of_non_proper_insts:           283
% 2.32/1.00  inst_num_of_duplicates:                 0
% 2.32/1.00  inst_inst_num_from_inst_to_res:         0
% 2.32/1.00  inst_dismatching_checking_time:         0.
% 2.32/1.00  
% 2.32/1.00  ------ Resolution
% 2.32/1.00  
% 2.32/1.00  res_num_of_clauses:                     0
% 2.32/1.00  res_num_in_passive:                     0
% 2.32/1.00  res_num_in_active:                      0
% 2.32/1.00  res_num_of_loops:                       165
% 2.32/1.00  res_forward_subset_subsumed:            48
% 2.32/1.00  res_backward_subset_subsumed:           0
% 2.32/1.00  res_forward_subsumed:                   0
% 2.32/1.00  res_backward_subsumed:                  0
% 2.32/1.00  res_forward_subsumption_resolution:     0
% 2.32/1.00  res_backward_subsumption_resolution:    0
% 2.32/1.00  res_clause_to_clause_subsumption:       160
% 2.32/1.00  res_orphan_elimination:                 0
% 2.32/1.00  res_tautology_del:                      50
% 2.32/1.00  res_num_eq_res_simplified:              0
% 2.32/1.00  res_num_sel_changes:                    0
% 2.32/1.00  res_moves_from_active_to_pass:          0
% 2.32/1.00  
% 2.32/1.00  ------ Superposition
% 2.32/1.00  
% 2.32/1.00  sup_time_total:                         0.
% 2.32/1.00  sup_time_generating:                    0.
% 2.32/1.00  sup_time_sim_full:                      0.
% 2.32/1.00  sup_time_sim_immed:                     0.
% 2.32/1.00  
% 2.32/1.00  sup_num_of_clauses:                     66
% 2.32/1.00  sup_num_in_active:                      54
% 2.32/1.00  sup_num_in_passive:                     12
% 2.32/1.00  sup_num_of_loops:                       55
% 2.32/1.00  sup_fw_superposition:                   32
% 2.32/1.00  sup_bw_superposition:                   7
% 2.32/1.00  sup_immediate_simplified:               5
% 2.32/1.00  sup_given_eliminated:                   0
% 2.32/1.00  comparisons_done:                       0
% 2.32/1.00  comparisons_avoided:                    0
% 2.32/1.00  
% 2.32/1.00  ------ Simplifications
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  sim_fw_subset_subsumed:                 0
% 2.32/1.00  sim_bw_subset_subsumed:                 1
% 2.32/1.00  sim_fw_subsumed:                        3
% 2.32/1.00  sim_bw_subsumed:                        0
% 2.32/1.00  sim_fw_subsumption_res:                 4
% 2.32/1.00  sim_bw_subsumption_res:                 0
% 2.32/1.00  sim_tautology_del:                      0
% 2.32/1.00  sim_eq_tautology_del:                   0
% 2.32/1.00  sim_eq_res_simp:                        0
% 2.32/1.00  sim_fw_demodulated:                     0
% 2.32/1.00  sim_bw_demodulated:                     1
% 2.32/1.00  sim_light_normalised:                   1
% 2.32/1.00  sim_joinable_taut:                      0
% 2.32/1.00  sim_joinable_simp:                      0
% 2.32/1.00  sim_ac_normalised:                      0
% 2.32/1.00  sim_smt_subsumption:                    0
% 2.32/1.00  
%------------------------------------------------------------------------------
