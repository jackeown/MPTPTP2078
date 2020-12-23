%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:50 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  302 (37925 expanded)
%              Number of clauses        :  203 (9351 expanded)
%              Number of leaves         :   22 (10886 expanded)
%              Depth                    :   33
%              Number of atoms          : 1325 (419714 expanded)
%              Number of equality atoms :  516 (53777 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | ~ v5_pre_topc(X2,X0,X1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | v5_pre_topc(X2,X0,X1) )
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
          & v1_funct_1(X3) )
     => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK3 = X2
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                | v5_pre_topc(X2,X0,X1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ v5_pre_topc(sK2,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK2,X0,X1) )
            & sK2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                  | ~ v5_pre_topc(X2,X0,sK1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                  | v5_pre_topc(X2,X0,sK1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f60,f59,f58,f57])).

fof(f103,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f61])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f102,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f120,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f48])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f109,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f67])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f114,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f110,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f66])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f94,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f95,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f96,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f97,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f101,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f106,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f104,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f61])).

fof(f100,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f61])).

fof(f99,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f105,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f38,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f89,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f87,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f119,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f116,plain,(
    ! [X1] :
      ( v1_partfun1(X1,k1_relat_1(X1))
      | ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f86])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1784,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1794,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6066,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1794])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1800,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4080,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1784,c_1800])).

cnf(c_6084,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6066,c_4080])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_6105,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6084])).

cnf(c_7710,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6084,c_36,c_6105])).

cnf(c_7711,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_7710])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1803,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_31,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1787,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3962,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1803,c_1787])).

cnf(c_10769,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(X0,X1,sK1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7711,c_3962])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_10857,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(X0,X1,sK1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10769,c_3])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_123,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_19,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1797,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1916,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1797,c_4])).

cnf(c_2049,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1916])).

cnf(c_2051,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2049])).

cnf(c_1804,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4078,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1804,c_1800])).

cnf(c_10,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4101,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4078,c_10])).

cnf(c_4110,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4101])).

cnf(c_951,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_5412,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != X2
    | u1_struct_0(sK0) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_951])).

cnf(c_5414,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != k1_xboole_0
    | u1_struct_0(sK0) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5412])).

cnf(c_7736,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7711,c_1784])).

cnf(c_7744,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7736,c_3])).

cnf(c_8122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7744])).

cnf(c_29,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1789,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5020,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1789])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_45,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_46,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_47,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_48,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_52,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_53,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_54,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,negated_conjecture,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1786,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_34,negated_conjecture,
    ( sK2 = sK3 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1904,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1786,c_34])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1781,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1835,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1781,c_34])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1780,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_1832,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1780,c_34])).

cnf(c_33,negated_conjecture,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1785,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1891,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1785,c_34])).

cnf(c_26,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2128,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2129,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2128])).

cnf(c_27,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2162,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2163,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2162])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2299,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2300,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2299])).

cnf(c_30,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2284,plain,
    ( v5_pre_topc(X0,sK0,X1)
    | ~ v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2690,plain,
    ( ~ v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(X0,sK0,sK1)
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_2284])).

cnf(c_3354,plain,
    ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2690])).

cnf(c_3355,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3354])).

cnf(c_2294,plain,
    ( ~ v5_pre_topc(X0,sK0,X1)
    | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2730,plain,
    ( v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(X0,sK0,sK1)
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_2294])).

cnf(c_3417,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2730])).

cnf(c_3418,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3417])).

cnf(c_28,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2264,plain,
    ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
    | v5_pre_topc(X0,sK0,X1)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2604,plain,
    ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_2264])).

cnf(c_3844,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2604])).

cnf(c_3845,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3844])).

cnf(c_5306,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5020,c_45,c_46,c_47,c_48,c_52,c_53,c_54,c_1904,c_1835,c_1832,c_1891,c_2129,c_2163,c_2300,c_3355,c_3418,c_3845])).

cnf(c_5307,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5306])).

cnf(c_5310,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5307,c_45,c_46,c_47,c_48,c_52,c_53,c_54,c_1835,c_1832,c_1891,c_2129,c_2163,c_2300,c_3418,c_3845])).

cnf(c_7732,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7711,c_5310])).

cnf(c_7766,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7732,c_3])).

cnf(c_8125,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7766])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1802,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3054,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1802])).

cnf(c_7735,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7711,c_3054])).

cnf(c_7749,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7735,c_3])).

cnf(c_3053,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1804,c_1802])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1806,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4898,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3053,c_1806])).

cnf(c_8861,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7749,c_4898])).

cnf(c_5316,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1803,c_5310])).

cnf(c_7731,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7711,c_5316])).

cnf(c_7773,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7731,c_3])).

cnf(c_9828,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7773,c_7744,c_7766])).

cnf(c_9829,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9828])).

cnf(c_9835,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7711,c_9829])).

cnf(c_4900,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
    | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3054,c_1806])).

cnf(c_7733,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7711,c_4900])).

cnf(c_7759,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7733,c_3])).

cnf(c_2919,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2920,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2919])).

cnf(c_2922,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2920])).

cnf(c_4508,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4511,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4508])).

cnf(c_9918,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7759,c_2922,c_4511])).

cnf(c_9919,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_9918])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1805,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4079,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1803,c_1800])).

cnf(c_5498,plain,
    ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1805,c_4079])).

cnf(c_9926,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_9919,c_5498])).

cnf(c_10068,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_9926,c_4080])).

cnf(c_10603,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_7711,c_10068])).

cnf(c_10655,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10603,c_3,c_10])).

cnf(c_1788,plain,
    ( v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4774,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1788])).

cnf(c_2131,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2132,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2131])).

cnf(c_2165,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2166,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2165])).

cnf(c_2303,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2304,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2303])).

cnf(c_2274,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
    | ~ v5_pre_topc(X0,sK0,X1)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2634,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(X0,sK0,sK1)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_2274])).

cnf(c_3330,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2634])).

cnf(c_3331,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3330])).

cnf(c_3963,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1787])).

cnf(c_2594,plain,
    ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(X0,sK0,sK1)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_2264])).

cnf(c_3306,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2594])).

cnf(c_3307,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3306])).

cnf(c_4426,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3963,c_45,c_46,c_47,c_48,c_52,c_53,c_1904,c_1835,c_1832,c_2132,c_2166,c_2304,c_3307])).

cnf(c_4427,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4426])).

cnf(c_4932,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4774,c_45,c_46,c_47,c_48,c_52,c_53,c_1835,c_1832,c_1891,c_2132,c_2166,c_2304,c_3331,c_4427])).

cnf(c_4933,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4932])).

cnf(c_11051,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10655,c_4933])).

cnf(c_1783,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_11057,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10655,c_1783])).

cnf(c_6067,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1835,c_1794])).

cnf(c_4081,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1835,c_1800])).

cnf(c_6077,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6067,c_4081])).

cnf(c_6188,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6077,c_1832])).

cnf(c_6189,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_6188])).

cnf(c_3055,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1835,c_1802])).

cnf(c_4901,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3055,c_1806])).

cnf(c_6208,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6189,c_4901])).

cnf(c_6296,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6208,c_3])).

cnf(c_6938,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6296,c_2922,c_4511])).

cnf(c_6939,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_6938])).

cnf(c_6944,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6939,c_5498])).

cnf(c_6986,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_6944,c_4081])).

cnf(c_7258,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6189,c_6986])).

cnf(c_7281,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7258,c_3,c_10])).

cnf(c_11056,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10655,c_1784])).

cnf(c_8374,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7281,c_5310])).

cnf(c_12039,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11056,c_8374])).

cnf(c_12105,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7281,c_12039])).

cnf(c_12114,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11051,c_11057,c_12105])).

cnf(c_6221,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6189,c_1832])).

cnf(c_12145,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12114,c_6221])).

cnf(c_13617,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10857,c_123,c_2051,c_4110,c_5414,c_7711,c_8122,c_8125,c_8861,c_9835,c_12145])).

cnf(c_13619,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13617,c_12114])).

cnf(c_13630,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13619,c_1784])).

cnf(c_13635,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13630,c_4])).

cnf(c_15,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_23,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v4_relat_1(X0,k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_535,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_536,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_546,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_536,c_12])).

cnf(c_581,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X3),X4)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_546])).

cnf(c_582,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_1773,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_12325,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),X0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12114,c_1773])).

cnf(c_12330,plain,
    ( v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12325,c_4,c_12114])).

cnf(c_12331,plain,
    ( v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12330,c_4])).

cnf(c_12560,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12331,c_52])).

cnf(c_12561,plain,
    ( v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12560])).

cnf(c_14479,plain,
    ( v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13635,c_12561])).

cnf(c_4938,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1803,c_4933])).

cnf(c_13625,plain,
    ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13619,c_4938])).

cnf(c_13661,plain,
    ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13625,c_4])).

cnf(c_13626,plain,
    ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13619,c_4933])).

cnf(c_13656,plain,
    ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13626,c_4])).

cnf(c_14939,plain,
    ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13661,c_13635,c_13656])).

cnf(c_15176,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_14479,c_14939])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:42:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.57/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.00  
% 3.57/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.57/1.00  
% 3.57/1.00  ------  iProver source info
% 3.57/1.00  
% 3.57/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.57/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.57/1.00  git: non_committed_changes: false
% 3.57/1.00  git: last_make_outside_of_git: false
% 3.57/1.00  
% 3.57/1.00  ------ 
% 3.57/1.00  
% 3.57/1.00  ------ Input Options
% 3.57/1.00  
% 3.57/1.00  --out_options                           all
% 3.57/1.00  --tptp_safe_out                         true
% 3.57/1.00  --problem_path                          ""
% 3.57/1.00  --include_path                          ""
% 3.57/1.00  --clausifier                            res/vclausify_rel
% 3.57/1.00  --clausifier_options                    --mode clausify
% 3.57/1.00  --stdin                                 false
% 3.57/1.00  --stats_out                             all
% 3.57/1.00  
% 3.57/1.00  ------ General Options
% 3.57/1.00  
% 3.57/1.00  --fof                                   false
% 3.57/1.00  --time_out_real                         305.
% 3.57/1.00  --time_out_virtual                      -1.
% 3.57/1.00  --symbol_type_check                     false
% 3.57/1.00  --clausify_out                          false
% 3.57/1.00  --sig_cnt_out                           false
% 3.57/1.00  --trig_cnt_out                          false
% 3.57/1.00  --trig_cnt_out_tolerance                1.
% 3.57/1.00  --trig_cnt_out_sk_spl                   false
% 3.57/1.00  --abstr_cl_out                          false
% 3.57/1.00  
% 3.57/1.00  ------ Global Options
% 3.57/1.00  
% 3.57/1.00  --schedule                              default
% 3.57/1.00  --add_important_lit                     false
% 3.57/1.00  --prop_solver_per_cl                    1000
% 3.57/1.00  --min_unsat_core                        false
% 3.57/1.00  --soft_assumptions                      false
% 3.57/1.00  --soft_lemma_size                       3
% 3.57/1.00  --prop_impl_unit_size                   0
% 3.57/1.00  --prop_impl_unit                        []
% 3.57/1.00  --share_sel_clauses                     true
% 3.57/1.00  --reset_solvers                         false
% 3.57/1.00  --bc_imp_inh                            [conj_cone]
% 3.57/1.00  --conj_cone_tolerance                   3.
% 3.57/1.00  --extra_neg_conj                        none
% 3.57/1.00  --large_theory_mode                     true
% 3.57/1.00  --prolific_symb_bound                   200
% 3.57/1.00  --lt_threshold                          2000
% 3.57/1.00  --clause_weak_htbl                      true
% 3.57/1.00  --gc_record_bc_elim                     false
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing Options
% 3.57/1.00  
% 3.57/1.00  --preprocessing_flag                    true
% 3.57/1.00  --time_out_prep_mult                    0.1
% 3.57/1.00  --splitting_mode                        input
% 3.57/1.00  --splitting_grd                         true
% 3.57/1.00  --splitting_cvd                         false
% 3.57/1.00  --splitting_cvd_svl                     false
% 3.57/1.00  --splitting_nvd                         32
% 3.57/1.00  --sub_typing                            true
% 3.57/1.00  --prep_gs_sim                           true
% 3.57/1.00  --prep_unflatten                        true
% 3.57/1.00  --prep_res_sim                          true
% 3.57/1.00  --prep_upred                            true
% 3.57/1.00  --prep_sem_filter                       exhaustive
% 3.57/1.00  --prep_sem_filter_out                   false
% 3.57/1.00  --pred_elim                             true
% 3.57/1.00  --res_sim_input                         true
% 3.57/1.00  --eq_ax_congr_red                       true
% 3.57/1.00  --pure_diseq_elim                       true
% 3.57/1.00  --brand_transform                       false
% 3.57/1.00  --non_eq_to_eq                          false
% 3.57/1.00  --prep_def_merge                        true
% 3.57/1.00  --prep_def_merge_prop_impl              false
% 3.57/1.00  --prep_def_merge_mbd                    true
% 3.57/1.00  --prep_def_merge_tr_red                 false
% 3.57/1.00  --prep_def_merge_tr_cl                  false
% 3.57/1.00  --smt_preprocessing                     true
% 3.57/1.00  --smt_ac_axioms                         fast
% 3.57/1.00  --preprocessed_out                      false
% 3.57/1.00  --preprocessed_stats                    false
% 3.57/1.00  
% 3.57/1.00  ------ Abstraction refinement Options
% 3.57/1.00  
% 3.57/1.00  --abstr_ref                             []
% 3.57/1.00  --abstr_ref_prep                        false
% 3.57/1.00  --abstr_ref_until_sat                   false
% 3.57/1.00  --abstr_ref_sig_restrict                funpre
% 3.57/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/1.00  --abstr_ref_under                       []
% 3.57/1.00  
% 3.57/1.00  ------ SAT Options
% 3.57/1.00  
% 3.57/1.00  --sat_mode                              false
% 3.57/1.00  --sat_fm_restart_options                ""
% 3.57/1.00  --sat_gr_def                            false
% 3.57/1.00  --sat_epr_types                         true
% 3.57/1.00  --sat_non_cyclic_types                  false
% 3.57/1.00  --sat_finite_models                     false
% 3.57/1.00  --sat_fm_lemmas                         false
% 3.57/1.00  --sat_fm_prep                           false
% 3.57/1.00  --sat_fm_uc_incr                        true
% 3.57/1.00  --sat_out_model                         small
% 3.57/1.00  --sat_out_clauses                       false
% 3.57/1.00  
% 3.57/1.00  ------ QBF Options
% 3.57/1.00  
% 3.57/1.00  --qbf_mode                              false
% 3.57/1.00  --qbf_elim_univ                         false
% 3.57/1.00  --qbf_dom_inst                          none
% 3.57/1.00  --qbf_dom_pre_inst                      false
% 3.57/1.00  --qbf_sk_in                             false
% 3.57/1.00  --qbf_pred_elim                         true
% 3.57/1.00  --qbf_split                             512
% 3.57/1.00  
% 3.57/1.00  ------ BMC1 Options
% 3.57/1.00  
% 3.57/1.00  --bmc1_incremental                      false
% 3.57/1.00  --bmc1_axioms                           reachable_all
% 3.57/1.00  --bmc1_min_bound                        0
% 3.57/1.00  --bmc1_max_bound                        -1
% 3.57/1.00  --bmc1_max_bound_default                -1
% 3.57/1.00  --bmc1_symbol_reachability              true
% 3.57/1.00  --bmc1_property_lemmas                  false
% 3.57/1.00  --bmc1_k_induction                      false
% 3.57/1.00  --bmc1_non_equiv_states                 false
% 3.57/1.00  --bmc1_deadlock                         false
% 3.57/1.00  --bmc1_ucm                              false
% 3.57/1.00  --bmc1_add_unsat_core                   none
% 3.57/1.00  --bmc1_unsat_core_children              false
% 3.57/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/1.00  --bmc1_out_stat                         full
% 3.57/1.00  --bmc1_ground_init                      false
% 3.57/1.00  --bmc1_pre_inst_next_state              false
% 3.57/1.00  --bmc1_pre_inst_state                   false
% 3.57/1.00  --bmc1_pre_inst_reach_state             false
% 3.57/1.00  --bmc1_out_unsat_core                   false
% 3.57/1.00  --bmc1_aig_witness_out                  false
% 3.57/1.00  --bmc1_verbose                          false
% 3.57/1.00  --bmc1_dump_clauses_tptp                false
% 3.57/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.57/1.00  --bmc1_dump_file                        -
% 3.57/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.57/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.57/1.00  --bmc1_ucm_extend_mode                  1
% 3.57/1.00  --bmc1_ucm_init_mode                    2
% 3.57/1.00  --bmc1_ucm_cone_mode                    none
% 3.57/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.57/1.00  --bmc1_ucm_relax_model                  4
% 3.57/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.57/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/1.00  --bmc1_ucm_layered_model                none
% 3.57/1.00  --bmc1_ucm_max_lemma_size               10
% 3.57/1.00  
% 3.57/1.00  ------ AIG Options
% 3.57/1.00  
% 3.57/1.00  --aig_mode                              false
% 3.57/1.00  
% 3.57/1.00  ------ Instantiation Options
% 3.57/1.00  
% 3.57/1.00  --instantiation_flag                    true
% 3.57/1.00  --inst_sos_flag                         false
% 3.57/1.00  --inst_sos_phase                        true
% 3.57/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/1.00  --inst_lit_sel_side                     num_symb
% 3.57/1.00  --inst_solver_per_active                1400
% 3.57/1.00  --inst_solver_calls_frac                1.
% 3.57/1.00  --inst_passive_queue_type               priority_queues
% 3.57/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/1.00  --inst_passive_queues_freq              [25;2]
% 3.57/1.00  --inst_dismatching                      true
% 3.57/1.00  --inst_eager_unprocessed_to_passive     true
% 3.57/1.00  --inst_prop_sim_given                   true
% 3.57/1.00  --inst_prop_sim_new                     false
% 3.57/1.00  --inst_subs_new                         false
% 3.57/1.00  --inst_eq_res_simp                      false
% 3.57/1.00  --inst_subs_given                       false
% 3.57/1.00  --inst_orphan_elimination               true
% 3.57/1.00  --inst_learning_loop_flag               true
% 3.57/1.00  --inst_learning_start                   3000
% 3.57/1.00  --inst_learning_factor                  2
% 3.57/1.00  --inst_start_prop_sim_after_learn       3
% 3.57/1.00  --inst_sel_renew                        solver
% 3.57/1.00  --inst_lit_activity_flag                true
% 3.57/1.00  --inst_restr_to_given                   false
% 3.57/1.00  --inst_activity_threshold               500
% 3.57/1.00  --inst_out_proof                        true
% 3.57/1.00  
% 3.57/1.00  ------ Resolution Options
% 3.57/1.00  
% 3.57/1.00  --resolution_flag                       true
% 3.57/1.00  --res_lit_sel                           adaptive
% 3.57/1.00  --res_lit_sel_side                      none
% 3.57/1.00  --res_ordering                          kbo
% 3.57/1.00  --res_to_prop_solver                    active
% 3.57/1.00  --res_prop_simpl_new                    false
% 3.57/1.00  --res_prop_simpl_given                  true
% 3.57/1.00  --res_passive_queue_type                priority_queues
% 3.57/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/1.00  --res_passive_queues_freq               [15;5]
% 3.57/1.00  --res_forward_subs                      full
% 3.57/1.00  --res_backward_subs                     full
% 3.57/1.00  --res_forward_subs_resolution           true
% 3.57/1.00  --res_backward_subs_resolution          true
% 3.57/1.00  --res_orphan_elimination                true
% 3.57/1.00  --res_time_limit                        2.
% 3.57/1.00  --res_out_proof                         true
% 3.57/1.00  
% 3.57/1.00  ------ Superposition Options
% 3.57/1.00  
% 3.57/1.00  --superposition_flag                    true
% 3.57/1.00  --sup_passive_queue_type                priority_queues
% 3.57/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.57/1.00  --demod_completeness_check              fast
% 3.57/1.00  --demod_use_ground                      true
% 3.57/1.00  --sup_to_prop_solver                    passive
% 3.57/1.00  --sup_prop_simpl_new                    true
% 3.57/1.00  --sup_prop_simpl_given                  true
% 3.57/1.00  --sup_fun_splitting                     false
% 3.57/1.00  --sup_smt_interval                      50000
% 3.57/1.00  
% 3.57/1.00  ------ Superposition Simplification Setup
% 3.57/1.00  
% 3.57/1.00  --sup_indices_passive                   []
% 3.57/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/1.00  --sup_full_bw                           [BwDemod]
% 3.57/1.00  --sup_immed_triv                        [TrivRules]
% 3.57/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/1.00  --sup_immed_bw_main                     []
% 3.57/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/1.00  
% 3.57/1.00  ------ Combination Options
% 3.57/1.00  
% 3.57/1.00  --comb_res_mult                         3
% 3.57/1.00  --comb_sup_mult                         2
% 3.57/1.00  --comb_inst_mult                        10
% 3.57/1.00  
% 3.57/1.00  ------ Debug Options
% 3.57/1.00  
% 3.57/1.00  --dbg_backtrace                         false
% 3.57/1.00  --dbg_dump_prop_clauses                 false
% 3.57/1.00  --dbg_dump_prop_clauses_file            -
% 3.57/1.00  --dbg_out_stat                          false
% 3.57/1.00  ------ Parsing...
% 3.57/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.57/1.00  ------ Proving...
% 3.57/1.00  ------ Problem Properties 
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  clauses                                 40
% 3.57/1.00  conjectures                             13
% 3.57/1.00  EPR                                     10
% 3.57/1.00  Horn                                    34
% 3.57/1.00  unary                                   17
% 3.57/1.00  binary                                  8
% 3.57/1.00  lits                                    115
% 3.57/1.00  lits eq                                 19
% 3.57/1.00  fd_pure                                 0
% 3.57/1.00  fd_pseudo                               0
% 3.57/1.00  fd_cond                                 4
% 3.57/1.00  fd_pseudo_cond                          1
% 3.57/1.00  AC symbols                              0
% 3.57/1.00  
% 3.57/1.00  ------ Schedule dynamic 5 is on 
% 3.57/1.00  
% 3.57/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  ------ 
% 3.57/1.00  Current options:
% 3.57/1.00  ------ 
% 3.57/1.00  
% 3.57/1.00  ------ Input Options
% 3.57/1.00  
% 3.57/1.00  --out_options                           all
% 3.57/1.00  --tptp_safe_out                         true
% 3.57/1.00  --problem_path                          ""
% 3.57/1.00  --include_path                          ""
% 3.57/1.00  --clausifier                            res/vclausify_rel
% 3.57/1.00  --clausifier_options                    --mode clausify
% 3.57/1.00  --stdin                                 false
% 3.57/1.00  --stats_out                             all
% 3.57/1.00  
% 3.57/1.00  ------ General Options
% 3.57/1.00  
% 3.57/1.00  --fof                                   false
% 3.57/1.00  --time_out_real                         305.
% 3.57/1.00  --time_out_virtual                      -1.
% 3.57/1.00  --symbol_type_check                     false
% 3.57/1.00  --clausify_out                          false
% 3.57/1.00  --sig_cnt_out                           false
% 3.57/1.00  --trig_cnt_out                          false
% 3.57/1.00  --trig_cnt_out_tolerance                1.
% 3.57/1.00  --trig_cnt_out_sk_spl                   false
% 3.57/1.00  --abstr_cl_out                          false
% 3.57/1.00  
% 3.57/1.00  ------ Global Options
% 3.57/1.00  
% 3.57/1.00  --schedule                              default
% 3.57/1.00  --add_important_lit                     false
% 3.57/1.00  --prop_solver_per_cl                    1000
% 3.57/1.00  --min_unsat_core                        false
% 3.57/1.00  --soft_assumptions                      false
% 3.57/1.00  --soft_lemma_size                       3
% 3.57/1.00  --prop_impl_unit_size                   0
% 3.57/1.00  --prop_impl_unit                        []
% 3.57/1.00  --share_sel_clauses                     true
% 3.57/1.00  --reset_solvers                         false
% 3.57/1.00  --bc_imp_inh                            [conj_cone]
% 3.57/1.00  --conj_cone_tolerance                   3.
% 3.57/1.00  --extra_neg_conj                        none
% 3.57/1.00  --large_theory_mode                     true
% 3.57/1.00  --prolific_symb_bound                   200
% 3.57/1.00  --lt_threshold                          2000
% 3.57/1.00  --clause_weak_htbl                      true
% 3.57/1.00  --gc_record_bc_elim                     false
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing Options
% 3.57/1.00  
% 3.57/1.00  --preprocessing_flag                    true
% 3.57/1.00  --time_out_prep_mult                    0.1
% 3.57/1.00  --splitting_mode                        input
% 3.57/1.00  --splitting_grd                         true
% 3.57/1.00  --splitting_cvd                         false
% 3.57/1.00  --splitting_cvd_svl                     false
% 3.57/1.00  --splitting_nvd                         32
% 3.57/1.00  --sub_typing                            true
% 3.57/1.00  --prep_gs_sim                           true
% 3.57/1.00  --prep_unflatten                        true
% 3.57/1.00  --prep_res_sim                          true
% 3.57/1.00  --prep_upred                            true
% 3.57/1.00  --prep_sem_filter                       exhaustive
% 3.57/1.00  --prep_sem_filter_out                   false
% 3.57/1.00  --pred_elim                             true
% 3.57/1.00  --res_sim_input                         true
% 3.57/1.00  --eq_ax_congr_red                       true
% 3.57/1.00  --pure_diseq_elim                       true
% 3.57/1.00  --brand_transform                       false
% 3.57/1.00  --non_eq_to_eq                          false
% 3.57/1.00  --prep_def_merge                        true
% 3.57/1.00  --prep_def_merge_prop_impl              false
% 3.57/1.00  --prep_def_merge_mbd                    true
% 3.57/1.00  --prep_def_merge_tr_red                 false
% 3.57/1.00  --prep_def_merge_tr_cl                  false
% 3.57/1.00  --smt_preprocessing                     true
% 3.57/1.00  --smt_ac_axioms                         fast
% 3.57/1.00  --preprocessed_out                      false
% 3.57/1.00  --preprocessed_stats                    false
% 3.57/1.00  
% 3.57/1.00  ------ Abstraction refinement Options
% 3.57/1.00  
% 3.57/1.00  --abstr_ref                             []
% 3.57/1.00  --abstr_ref_prep                        false
% 3.57/1.00  --abstr_ref_until_sat                   false
% 3.57/1.00  --abstr_ref_sig_restrict                funpre
% 3.57/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/1.00  --abstr_ref_under                       []
% 3.57/1.00  
% 3.57/1.00  ------ SAT Options
% 3.57/1.00  
% 3.57/1.00  --sat_mode                              false
% 3.57/1.00  --sat_fm_restart_options                ""
% 3.57/1.00  --sat_gr_def                            false
% 3.57/1.00  --sat_epr_types                         true
% 3.57/1.00  --sat_non_cyclic_types                  false
% 3.57/1.00  --sat_finite_models                     false
% 3.57/1.00  --sat_fm_lemmas                         false
% 3.57/1.00  --sat_fm_prep                           false
% 3.57/1.00  --sat_fm_uc_incr                        true
% 3.57/1.00  --sat_out_model                         small
% 3.57/1.00  --sat_out_clauses                       false
% 3.57/1.00  
% 3.57/1.00  ------ QBF Options
% 3.57/1.00  
% 3.57/1.00  --qbf_mode                              false
% 3.57/1.00  --qbf_elim_univ                         false
% 3.57/1.00  --qbf_dom_inst                          none
% 3.57/1.00  --qbf_dom_pre_inst                      false
% 3.57/1.00  --qbf_sk_in                             false
% 3.57/1.00  --qbf_pred_elim                         true
% 3.57/1.00  --qbf_split                             512
% 3.57/1.00  
% 3.57/1.00  ------ BMC1 Options
% 3.57/1.00  
% 3.57/1.00  --bmc1_incremental                      false
% 3.57/1.00  --bmc1_axioms                           reachable_all
% 3.57/1.00  --bmc1_min_bound                        0
% 3.57/1.00  --bmc1_max_bound                        -1
% 3.57/1.00  --bmc1_max_bound_default                -1
% 3.57/1.00  --bmc1_symbol_reachability              true
% 3.57/1.00  --bmc1_property_lemmas                  false
% 3.57/1.00  --bmc1_k_induction                      false
% 3.57/1.00  --bmc1_non_equiv_states                 false
% 3.57/1.00  --bmc1_deadlock                         false
% 3.57/1.00  --bmc1_ucm                              false
% 3.57/1.00  --bmc1_add_unsat_core                   none
% 3.57/1.00  --bmc1_unsat_core_children              false
% 3.57/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/1.00  --bmc1_out_stat                         full
% 3.57/1.00  --bmc1_ground_init                      false
% 3.57/1.00  --bmc1_pre_inst_next_state              false
% 3.57/1.00  --bmc1_pre_inst_state                   false
% 3.57/1.00  --bmc1_pre_inst_reach_state             false
% 3.57/1.00  --bmc1_out_unsat_core                   false
% 3.57/1.00  --bmc1_aig_witness_out                  false
% 3.57/1.00  --bmc1_verbose                          false
% 3.57/1.00  --bmc1_dump_clauses_tptp                false
% 3.57/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.57/1.00  --bmc1_dump_file                        -
% 3.57/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.57/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.57/1.00  --bmc1_ucm_extend_mode                  1
% 3.57/1.00  --bmc1_ucm_init_mode                    2
% 3.57/1.00  --bmc1_ucm_cone_mode                    none
% 3.57/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.57/1.00  --bmc1_ucm_relax_model                  4
% 3.57/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.57/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/1.00  --bmc1_ucm_layered_model                none
% 3.57/1.00  --bmc1_ucm_max_lemma_size               10
% 3.57/1.00  
% 3.57/1.00  ------ AIG Options
% 3.57/1.00  
% 3.57/1.00  --aig_mode                              false
% 3.57/1.00  
% 3.57/1.00  ------ Instantiation Options
% 3.57/1.00  
% 3.57/1.00  --instantiation_flag                    true
% 3.57/1.00  --inst_sos_flag                         false
% 3.57/1.00  --inst_sos_phase                        true
% 3.57/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/1.00  --inst_lit_sel_side                     none
% 3.57/1.00  --inst_solver_per_active                1400
% 3.57/1.00  --inst_solver_calls_frac                1.
% 3.57/1.00  --inst_passive_queue_type               priority_queues
% 3.57/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/1.00  --inst_passive_queues_freq              [25;2]
% 3.57/1.00  --inst_dismatching                      true
% 3.57/1.00  --inst_eager_unprocessed_to_passive     true
% 3.57/1.00  --inst_prop_sim_given                   true
% 3.57/1.00  --inst_prop_sim_new                     false
% 3.57/1.00  --inst_subs_new                         false
% 3.57/1.00  --inst_eq_res_simp                      false
% 3.57/1.00  --inst_subs_given                       false
% 3.57/1.00  --inst_orphan_elimination               true
% 3.57/1.00  --inst_learning_loop_flag               true
% 3.57/1.00  --inst_learning_start                   3000
% 3.57/1.00  --inst_learning_factor                  2
% 3.57/1.00  --inst_start_prop_sim_after_learn       3
% 3.57/1.00  --inst_sel_renew                        solver
% 3.57/1.00  --inst_lit_activity_flag                true
% 3.57/1.00  --inst_restr_to_given                   false
% 3.57/1.00  --inst_activity_threshold               500
% 3.57/1.00  --inst_out_proof                        true
% 3.57/1.00  
% 3.57/1.00  ------ Resolution Options
% 3.57/1.00  
% 3.57/1.00  --resolution_flag                       false
% 3.57/1.00  --res_lit_sel                           adaptive
% 3.57/1.00  --res_lit_sel_side                      none
% 3.57/1.00  --res_ordering                          kbo
% 3.57/1.00  --res_to_prop_solver                    active
% 3.57/1.00  --res_prop_simpl_new                    false
% 3.57/1.00  --res_prop_simpl_given                  true
% 3.57/1.00  --res_passive_queue_type                priority_queues
% 3.57/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/1.00  --res_passive_queues_freq               [15;5]
% 3.57/1.00  --res_forward_subs                      full
% 3.57/1.00  --res_backward_subs                     full
% 3.57/1.00  --res_forward_subs_resolution           true
% 3.57/1.00  --res_backward_subs_resolution          true
% 3.57/1.00  --res_orphan_elimination                true
% 3.57/1.00  --res_time_limit                        2.
% 3.57/1.00  --res_out_proof                         true
% 3.57/1.00  
% 3.57/1.00  ------ Superposition Options
% 3.57/1.00  
% 3.57/1.00  --superposition_flag                    true
% 3.57/1.00  --sup_passive_queue_type                priority_queues
% 3.57/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.57/1.00  --demod_completeness_check              fast
% 3.57/1.00  --demod_use_ground                      true
% 3.57/1.00  --sup_to_prop_solver                    passive
% 3.57/1.00  --sup_prop_simpl_new                    true
% 3.57/1.00  --sup_prop_simpl_given                  true
% 3.57/1.00  --sup_fun_splitting                     false
% 3.57/1.00  --sup_smt_interval                      50000
% 3.57/1.00  
% 3.57/1.00  ------ Superposition Simplification Setup
% 3.57/1.00  
% 3.57/1.00  --sup_indices_passive                   []
% 3.57/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/1.00  --sup_full_bw                           [BwDemod]
% 3.57/1.00  --sup_immed_triv                        [TrivRules]
% 3.57/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/1.00  --sup_immed_bw_main                     []
% 3.57/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/1.00  
% 3.57/1.00  ------ Combination Options
% 3.57/1.00  
% 3.57/1.00  --comb_res_mult                         3
% 3.57/1.00  --comb_sup_mult                         2
% 3.57/1.00  --comb_inst_mult                        10
% 3.57/1.00  
% 3.57/1.00  ------ Debug Options
% 3.57/1.00  
% 3.57/1.00  --dbg_backtrace                         false
% 3.57/1.00  --dbg_dump_prop_clauses                 false
% 3.57/1.00  --dbg_dump_prop_clauses_file            -
% 3.57/1.00  --dbg_out_stat                          false
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  ------ Proving...
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  % SZS status Theorem for theBenchmark.p
% 3.57/1.00  
% 3.57/1.00   Resolution empty clause
% 3.57/1.00  
% 3.57/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.57/1.00  
% 3.57/1.00  fof(f19,conjecture,(
% 3.57/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f20,negated_conjecture,(
% 3.57/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.57/1.00    inference(negated_conjecture,[],[f19])).
% 3.57/1.00  
% 3.57/1.00  fof(f44,plain,(
% 3.57/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.57/1.00    inference(ennf_transformation,[],[f20])).
% 3.57/1.00  
% 3.57/1.00  fof(f45,plain,(
% 3.57/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.57/1.00    inference(flattening,[],[f44])).
% 3.57/1.00  
% 3.57/1.00  fof(f55,plain,(
% 3.57/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.57/1.00    inference(nnf_transformation,[],[f45])).
% 3.57/1.00  
% 3.57/1.00  fof(f56,plain,(
% 3.57/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.57/1.00    inference(flattening,[],[f55])).
% 3.57/1.00  
% 3.57/1.00  fof(f60,plain,(
% 3.57/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK3 = X2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK3))) )),
% 3.57/1.00    introduced(choice_axiom,[])).
% 3.57/1.00  
% 3.57/1.00  fof(f59,plain,(
% 3.57/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.57/1.00    introduced(choice_axiom,[])).
% 3.57/1.00  
% 3.57/1.00  fof(f58,plain,(
% 3.57/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,X0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,X0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 3.57/1.00    introduced(choice_axiom,[])).
% 3.57/1.00  
% 3.57/1.00  fof(f57,plain,(
% 3.57/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.57/1.00    introduced(choice_axiom,[])).
% 3.57/1.00  
% 3.57/1.00  fof(f61,plain,(
% 3.57/1.00    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.57/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f60,f59,f58,f57])).
% 3.57/1.00  
% 3.57/1.00  fof(f103,plain,(
% 3.57/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.57/1.00    inference(cnf_transformation,[],[f61])).
% 3.57/1.00  
% 3.57/1.00  fof(f12,axiom,(
% 3.57/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f32,plain,(
% 3.57/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/1.00    inference(ennf_transformation,[],[f12])).
% 3.57/1.00  
% 3.57/1.00  fof(f33,plain,(
% 3.57/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/1.00    inference(flattening,[],[f32])).
% 3.57/1.00  
% 3.57/1.00  fof(f51,plain,(
% 3.57/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/1.00    inference(nnf_transformation,[],[f33])).
% 3.57/1.00  
% 3.57/1.00  fof(f79,plain,(
% 3.57/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f51])).
% 3.57/1.00  
% 3.57/1.00  fof(f10,axiom,(
% 3.57/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f29,plain,(
% 3.57/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/1.00    inference(ennf_transformation,[],[f10])).
% 3.57/1.00  
% 3.57/1.00  fof(f76,plain,(
% 3.57/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f29])).
% 3.57/1.00  
% 3.57/1.00  fof(f102,plain,(
% 3.57/1.00    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.57/1.00    inference(cnf_transformation,[],[f61])).
% 3.57/1.00  
% 3.57/1.00  fof(f4,axiom,(
% 3.57/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f50,plain,(
% 3.57/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.57/1.00    inference(nnf_transformation,[],[f4])).
% 3.57/1.00  
% 3.57/1.00  fof(f70,plain,(
% 3.57/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f50])).
% 3.57/1.00  
% 3.57/1.00  fof(f18,axiom,(
% 3.57/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f42,plain,(
% 3.57/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.57/1.00    inference(ennf_transformation,[],[f18])).
% 3.57/1.00  
% 3.57/1.00  fof(f43,plain,(
% 3.57/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.57/1.00    inference(flattening,[],[f42])).
% 3.57/1.00  
% 3.57/1.00  fof(f54,plain,(
% 3.57/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.57/1.00    inference(nnf_transformation,[],[f43])).
% 3.57/1.00  
% 3.57/1.00  fof(f92,plain,(
% 3.57/1.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f54])).
% 3.57/1.00  
% 3.57/1.00  fof(f120,plain,(
% 3.57/1.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/1.00    inference(equality_resolution,[],[f92])).
% 3.57/1.00  
% 3.57/1.00  fof(f2,axiom,(
% 3.57/1.00    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f48,plain,(
% 3.57/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.57/1.00    inference(nnf_transformation,[],[f2])).
% 3.57/1.00  
% 3.57/1.00  fof(f49,plain,(
% 3.57/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.57/1.00    inference(flattening,[],[f48])).
% 3.57/1.00  
% 3.57/1.00  fof(f67,plain,(
% 3.57/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.57/1.00    inference(cnf_transformation,[],[f49])).
% 3.57/1.00  
% 3.57/1.00  fof(f109,plain,(
% 3.57/1.00    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.57/1.00    inference(equality_resolution,[],[f67])).
% 3.57/1.00  
% 3.57/1.00  fof(f3,axiom,(
% 3.57/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f68,plain,(
% 3.57/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f3])).
% 3.57/1.00  
% 3.57/1.00  fof(f82,plain,(
% 3.57/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f51])).
% 3.57/1.00  
% 3.57/1.00  fof(f114,plain,(
% 3.57/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.57/1.00    inference(equality_resolution,[],[f82])).
% 3.57/1.00  
% 3.57/1.00  fof(f66,plain,(
% 3.57/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.57/1.00    inference(cnf_transformation,[],[f49])).
% 3.57/1.00  
% 3.57/1.00  fof(f110,plain,(
% 3.57/1.00    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.57/1.00    inference(equality_resolution,[],[f66])).
% 3.57/1.00  
% 3.57/1.00  fof(f6,axiom,(
% 3.57/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f71,plain,(
% 3.57/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.57/1.00    inference(cnf_transformation,[],[f6])).
% 3.57/1.00  
% 3.57/1.00  fof(f17,axiom,(
% 3.57/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f40,plain,(
% 3.57/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.57/1.00    inference(ennf_transformation,[],[f17])).
% 3.57/1.00  
% 3.57/1.00  fof(f41,plain,(
% 3.57/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.57/1.00    inference(flattening,[],[f40])).
% 3.57/1.00  
% 3.57/1.00  fof(f53,plain,(
% 3.57/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.57/1.00    inference(nnf_transformation,[],[f41])).
% 3.57/1.00  
% 3.57/1.00  fof(f90,plain,(
% 3.57/1.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f53])).
% 3.57/1.00  
% 3.57/1.00  fof(f118,plain,(
% 3.57/1.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/1.00    inference(equality_resolution,[],[f90])).
% 3.57/1.00  
% 3.57/1.00  fof(f94,plain,(
% 3.57/1.00    v2_pre_topc(sK0)),
% 3.57/1.00    inference(cnf_transformation,[],[f61])).
% 3.57/1.00  
% 3.57/1.00  fof(f95,plain,(
% 3.57/1.00    l1_pre_topc(sK0)),
% 3.57/1.00    inference(cnf_transformation,[],[f61])).
% 3.57/1.00  
% 3.57/1.00  fof(f96,plain,(
% 3.57/1.00    v2_pre_topc(sK1)),
% 3.57/1.00    inference(cnf_transformation,[],[f61])).
% 3.57/1.00  
% 3.57/1.00  fof(f97,plain,(
% 3.57/1.00    l1_pre_topc(sK1)),
% 3.57/1.00    inference(cnf_transformation,[],[f61])).
% 3.57/1.00  
% 3.57/1.00  fof(f101,plain,(
% 3.57/1.00    v1_funct_1(sK3)),
% 3.57/1.00    inference(cnf_transformation,[],[f61])).
% 3.57/1.00  
% 3.57/1.00  fof(f106,plain,(
% 3.57/1.00    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 3.57/1.00    inference(cnf_transformation,[],[f61])).
% 3.57/1.00  
% 3.57/1.00  fof(f104,plain,(
% 3.57/1.00    sK2 = sK3),
% 3.57/1.00    inference(cnf_transformation,[],[f61])).
% 3.57/1.00  
% 3.57/1.00  fof(f100,plain,(
% 3.57/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.57/1.00    inference(cnf_transformation,[],[f61])).
% 3.57/1.00  
% 3.57/1.00  fof(f99,plain,(
% 3.57/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.57/1.00    inference(cnf_transformation,[],[f61])).
% 3.57/1.00  
% 3.57/1.00  fof(f105,plain,(
% 3.57/1.00    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 3.57/1.00    inference(cnf_transformation,[],[f61])).
% 3.57/1.00  
% 3.57/1.00  fof(f15,axiom,(
% 3.57/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f37,plain,(
% 3.57/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/1.00    inference(ennf_transformation,[],[f15])).
% 3.57/1.00  
% 3.57/1.00  fof(f88,plain,(
% 3.57/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f37])).
% 3.57/1.00  
% 3.57/1.00  fof(f16,axiom,(
% 3.57/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f22,plain,(
% 3.57/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 3.57/1.00    inference(pure_predicate_removal,[],[f16])).
% 3.57/1.00  
% 3.57/1.00  fof(f38,plain,(
% 3.57/1.00    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.57/1.00    inference(ennf_transformation,[],[f22])).
% 3.57/1.00  
% 3.57/1.00  fof(f39,plain,(
% 3.57/1.00    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.57/1.00    inference(flattening,[],[f38])).
% 3.57/1.00  
% 3.57/1.00  fof(f89,plain,(
% 3.57/1.00    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f39])).
% 3.57/1.00  
% 3.57/1.00  fof(f14,axiom,(
% 3.57/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f21,plain,(
% 3.57/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 3.57/1.00    inference(pure_predicate_removal,[],[f14])).
% 3.57/1.00  
% 3.57/1.00  fof(f36,plain,(
% 3.57/1.00    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.57/1.00    inference(ennf_transformation,[],[f21])).
% 3.57/1.00  
% 3.57/1.00  fof(f87,plain,(
% 3.57/1.00    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f36])).
% 3.57/1.00  
% 3.57/1.00  fof(f93,plain,(
% 3.57/1.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f54])).
% 3.57/1.00  
% 3.57/1.00  fof(f119,plain,(
% 3.57/1.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/1.00    inference(equality_resolution,[],[f93])).
% 3.57/1.00  
% 3.57/1.00  fof(f91,plain,(
% 3.57/1.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f53])).
% 3.57/1.00  
% 3.57/1.00  fof(f117,plain,(
% 3.57/1.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/1.00    inference(equality_resolution,[],[f91])).
% 3.57/1.00  
% 3.57/1.00  fof(f69,plain,(
% 3.57/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f50])).
% 3.57/1.00  
% 3.57/1.00  fof(f1,axiom,(
% 3.57/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f46,plain,(
% 3.57/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.57/1.00    inference(nnf_transformation,[],[f1])).
% 3.57/1.00  
% 3.57/1.00  fof(f47,plain,(
% 3.57/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.57/1.00    inference(flattening,[],[f46])).
% 3.57/1.00  
% 3.57/1.00  fof(f64,plain,(
% 3.57/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f47])).
% 3.57/1.00  
% 3.57/1.00  fof(f63,plain,(
% 3.57/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.57/1.00    inference(cnf_transformation,[],[f47])).
% 3.57/1.00  
% 3.57/1.00  fof(f107,plain,(
% 3.57/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.57/1.00    inference(equality_resolution,[],[f63])).
% 3.57/1.00  
% 3.57/1.00  fof(f11,axiom,(
% 3.57/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f30,plain,(
% 3.57/1.00    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/1.00    inference(ennf_transformation,[],[f11])).
% 3.57/1.00  
% 3.57/1.00  fof(f31,plain,(
% 3.57/1.00    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/1.00    inference(flattening,[],[f30])).
% 3.57/1.00  
% 3.57/1.00  fof(f78,plain,(
% 3.57/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f31])).
% 3.57/1.00  
% 3.57/1.00  fof(f9,axiom,(
% 3.57/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f23,plain,(
% 3.57/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.57/1.00    inference(pure_predicate_removal,[],[f9])).
% 3.57/1.00  
% 3.57/1.00  fof(f28,plain,(
% 3.57/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/1.00    inference(ennf_transformation,[],[f23])).
% 3.57/1.00  
% 3.57/1.00  fof(f75,plain,(
% 3.57/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f28])).
% 3.57/1.00  
% 3.57/1.00  fof(f13,axiom,(
% 3.57/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f34,plain,(
% 3.57/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.57/1.00    inference(ennf_transformation,[],[f13])).
% 3.57/1.00  
% 3.57/1.00  fof(f35,plain,(
% 3.57/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.57/1.00    inference(flattening,[],[f34])).
% 3.57/1.00  
% 3.57/1.00  fof(f52,plain,(
% 3.57/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.57/1.00    inference(nnf_transformation,[],[f35])).
% 3.57/1.00  
% 3.57/1.00  fof(f86,plain,(
% 3.57/1.00    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f52])).
% 3.57/1.00  
% 3.57/1.00  fof(f116,plain,(
% 3.57/1.00    ( ! [X1] : (v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.57/1.00    inference(equality_resolution,[],[f86])).
% 3.57/1.00  
% 3.57/1.00  fof(f8,axiom,(
% 3.57/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f27,plain,(
% 3.57/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/1.00    inference(ennf_transformation,[],[f8])).
% 3.57/1.00  
% 3.57/1.00  fof(f74,plain,(
% 3.57/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f27])).
% 3.57/1.00  
% 3.57/1.00  cnf(c_35,negated_conjecture,
% 3.57/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
% 3.57/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1784,plain,
% 3.57/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_22,plain,
% 3.57/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.57/1.00      | k1_xboole_0 = X2 ),
% 3.57/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1794,plain,
% 3.57/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.57/1.00      | k1_xboole_0 = X1
% 3.57/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.57/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6066,plain,
% 3.57/1.00      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1784,c_1794]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_14,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1800,plain,
% 3.57/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.57/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4080,plain,
% 3.57/1.00      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1784,c_1800]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6084,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.57/1.00      inference(light_normalisation,[status(thm)],[c_6066,c_4080]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_36,negated_conjecture,
% 3.57/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
% 3.57/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6105,plain,
% 3.57/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6084]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7710,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0 ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_6084,c_36,c_6105]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7711,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(renaming,[status(thm)],[c_7710]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7,plain,
% 3.57/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.57/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1803,plain,
% 3.57/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.57/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_31,plain,
% 3.57/1.00      ( ~ v5_pre_topc(X0,X1,X2)
% 3.57/1.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 3.57/1.00      | ~ v2_pre_topc(X1)
% 3.57/1.00      | ~ v2_pre_topc(X2)
% 3.57/1.00      | ~ l1_pre_topc(X1)
% 3.57/1.00      | ~ l1_pre_topc(X2)
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f120]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1787,plain,
% 3.57/1.00      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.57/1.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 3.57/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.57/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 3.57/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.57/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 3.57/1.00      | v2_pre_topc(X1) != iProver_top
% 3.57/1.00      | v2_pre_topc(X2) != iProver_top
% 3.57/1.00      | l1_pre_topc(X1) != iProver_top
% 3.57/1.00      | l1_pre_topc(X2) != iProver_top
% 3.57/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3962,plain,
% 3.57/1.00      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.57/1.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 3.57/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.57/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 3.57/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.57/1.00      | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))) != iProver_top
% 3.57/1.00      | v2_pre_topc(X1) != iProver_top
% 3.57/1.00      | v2_pre_topc(X2) != iProver_top
% 3.57/1.00      | l1_pre_topc(X1) != iProver_top
% 3.57/1.00      | l1_pre_topc(X2) != iProver_top
% 3.57/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1803,c_1787]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_10769,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.57/1.00      | v5_pre_topc(X0,X1,sK1) != iProver_top
% 3.57/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
% 3.57/1.00      | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)) != iProver_top
% 3.57/1.00      | v2_pre_topc(X1) != iProver_top
% 3.57/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.57/1.00      | l1_pre_topc(X1) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.57/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_7711,c_3962]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3,plain,
% 3.57/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.57/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_10857,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.57/1.00      | v5_pre_topc(X0,X1,sK1) != iProver_top
% 3.57/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
% 3.57/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.57/1.00      | v2_pre_topc(X1) != iProver_top
% 3.57/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.57/1.00      | l1_pre_topc(X1) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.57/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_10769,c_3]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6,plain,
% 3.57/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.57/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_123,plain,
% 3.57/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_19,plain,
% 3.57/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.57/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.57/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1797,plain,
% 3.57/1.00      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 3.57/1.00      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 3.57/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4,plain,
% 3.57/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.57/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1916,plain,
% 3.57/1.00      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 3.57/1.00      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 3.57/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.57/1.00      inference(light_normalisation,[status(thm)],[c_1797,c_4]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2049,plain,
% 3.57/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 3.57/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.57/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1916]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2051,plain,
% 3.57/1.00      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.57/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.57/1.00      | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_2049]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1804,plain,
% 3.57/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4078,plain,
% 3.57/1.00      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1804,c_1800]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_10,plain,
% 3.57/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.57/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4101,plain,
% 3.57/1.00      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 3.57/1.00      inference(light_normalisation,[status(thm)],[c_4078,c_10]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4110,plain,
% 3.57/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_4101]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_951,plain,
% 3.57/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.57/1.00      | v1_funct_2(X3,X4,X5)
% 3.57/1.00      | X3 != X0
% 3.57/1.00      | X4 != X1
% 3.57/1.00      | X5 != X2 ),
% 3.57/1.00      theory(equality) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_5412,plain,
% 3.57/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != X2
% 3.57/1.00      | u1_struct_0(sK0) != X1
% 3.57/1.00      | sK3 != X0 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_951]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_5414,plain,
% 3.57/1.00      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.57/1.00      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != k1_xboole_0
% 3.57/1.00      | u1_struct_0(sK0) != k1_xboole_0
% 3.57/1.00      | sK3 != k1_xboole_0 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_5412]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7736,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_7711,c_1784]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7744,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_7736,c_3]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_8122,plain,
% 3.57/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7744]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_29,plain,
% 3.57/1.00      ( ~ v5_pre_topc(X0,X1,X2)
% 3.57/1.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 3.57/1.00      | ~ v2_pre_topc(X1)
% 3.57/1.00      | ~ v2_pre_topc(X2)
% 3.57/1.00      | ~ l1_pre_topc(X1)
% 3.57/1.00      | ~ l1_pre_topc(X2)
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f118]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1789,plain,
% 3.57/1.00      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.57/1.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 3.57/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.57/1.00      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 3.57/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.57/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 3.57/1.00      | v2_pre_topc(X1) != iProver_top
% 3.57/1.00      | v2_pre_topc(X2) != iProver_top
% 3.57/1.00      | l1_pre_topc(X1) != iProver_top
% 3.57/1.00      | l1_pre_topc(X2) != iProver_top
% 3.57/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_5020,plain,
% 3.57/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.57/1.00      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.57/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.57/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.57/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.57/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1784,c_1789]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_44,negated_conjecture,
% 3.57/1.00      ( v2_pre_topc(sK0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_45,plain,
% 3.57/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_43,negated_conjecture,
% 3.57/1.00      ( l1_pre_topc(sK0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_46,plain,
% 3.57/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_42,negated_conjecture,
% 3.57/1.00      ( v2_pre_topc(sK1) ),
% 3.57/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_47,plain,
% 3.57/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_41,negated_conjecture,
% 3.57/1.00      ( l1_pre_topc(sK1) ),
% 3.57/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_48,plain,
% 3.57/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_37,negated_conjecture,
% 3.57/1.00      ( v1_funct_1(sK3) ),
% 3.57/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_52,plain,
% 3.57/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_53,plain,
% 3.57/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_54,plain,
% 3.57/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_32,negated_conjecture,
% 3.57/1.00      ( ~ v5_pre_topc(sK2,sK0,sK1)
% 3.57/1.00      | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.57/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1786,plain,
% 3.57/1.00      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
% 3.57/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_34,negated_conjecture,
% 3.57/1.00      ( sK2 = sK3 ),
% 3.57/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1904,plain,
% 3.57/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.57/1.00      | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
% 3.57/1.00      inference(light_normalisation,[status(thm)],[c_1786,c_34]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_38,negated_conjecture,
% 3.57/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.57/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1781,plain,
% 3.57/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1835,plain,
% 3.57/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.57/1.00      inference(light_normalisation,[status(thm)],[c_1781,c_34]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_39,negated_conjecture,
% 3.57/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.57/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1780,plain,
% 3.57/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1832,plain,
% 3.57/1.00      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.57/1.00      inference(light_normalisation,[status(thm)],[c_1780,c_34]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_33,negated_conjecture,
% 3.57/1.00      ( v5_pre_topc(sK2,sK0,sK1)
% 3.57/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.57/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1785,plain,
% 3.57/1.00      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
% 3.57/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1891,plain,
% 3.57/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.57/1.00      | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
% 3.57/1.00      inference(light_normalisation,[status(thm)],[c_1785,c_34]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_26,plain,
% 3.57/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.57/1.00      | ~ l1_pre_topc(X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2128,plain,
% 3.57/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.57/1.00      | ~ l1_pre_topc(sK1) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2129,plain,
% 3.57/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 3.57/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_2128]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_27,plain,
% 3.57/1.00      ( ~ v2_pre_topc(X0)
% 3.57/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.57/1.00      | ~ l1_pre_topc(X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2162,plain,
% 3.57/1.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.57/1.00      | ~ v2_pre_topc(sK1)
% 3.57/1.00      | ~ l1_pre_topc(sK1) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_27]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2163,plain,
% 3.57/1.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.57/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_2162]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_25,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.57/1.00      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.57/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2299,plain,
% 3.57/1.00      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.57/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2300,plain,
% 3.57/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.57/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_2299]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_30,plain,
% 3.57/1.00      ( v5_pre_topc(X0,X1,X2)
% 3.57/1.00      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 3.57/1.00      | ~ v2_pre_topc(X1)
% 3.57/1.00      | ~ v2_pre_topc(X2)
% 3.57/1.00      | ~ l1_pre_topc(X1)
% 3.57/1.00      | ~ l1_pre_topc(X2)
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f119]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2284,plain,
% 3.57/1.00      ( v5_pre_topc(X0,sK0,X1)
% 3.57/1.00      | ~ v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 3.57/1.00      | ~ v2_pre_topc(X1)
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(X1)
% 3.57/1.00      | ~ l1_pre_topc(sK0)
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_30]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2690,plain,
% 3.57/1.00      ( ~ v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.57/1.00      | v5_pre_topc(X0,sK0,sK1)
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.57/1.00      | ~ v2_pre_topc(sK1)
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(sK1)
% 3.57/1.00      | ~ l1_pre_topc(sK0)
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_2284]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3354,plain,
% 3.57/1.00      ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.57/1.00      | v5_pre_topc(sK3,sK0,sK1)
% 3.57/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.57/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.57/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.57/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.57/1.00      | ~ v2_pre_topc(sK1)
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(sK1)
% 3.57/1.00      | ~ l1_pre_topc(sK0)
% 3.57/1.00      | ~ v1_funct_1(sK3) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_2690]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3355,plain,
% 3.57/1.00      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.57/1.00      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.57/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.57/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.57/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_3354]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2294,plain,
% 3.57/1.00      ( ~ v5_pre_topc(X0,sK0,X1)
% 3.57/1.00      | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 3.57/1.00      | ~ v2_pre_topc(X1)
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(X1)
% 3.57/1.00      | ~ l1_pre_topc(sK0)
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_31]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2730,plain,
% 3.57/1.00      ( v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.57/1.00      | ~ v5_pre_topc(X0,sK0,sK1)
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.57/1.00      | ~ v2_pre_topc(sK1)
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(sK1)
% 3.57/1.00      | ~ l1_pre_topc(sK0)
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_2294]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3417,plain,
% 3.57/1.00      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.57/1.00      | ~ v5_pre_topc(sK3,sK0,sK1)
% 3.57/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.57/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.57/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.57/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.57/1.00      | ~ v2_pre_topc(sK1)
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(sK1)
% 3.57/1.00      | ~ l1_pre_topc(sK0)
% 3.57/1.00      | ~ v1_funct_1(sK3) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_2730]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3418,plain,
% 3.57/1.00      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.57/1.00      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.57/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.57/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.57/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_3417]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_28,plain,
% 3.57/1.00      ( v5_pre_topc(X0,X1,X2)
% 3.57/1.00      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 3.57/1.00      | ~ v2_pre_topc(X1)
% 3.57/1.00      | ~ v2_pre_topc(X2)
% 3.57/1.00      | ~ l1_pre_topc(X1)
% 3.57/1.00      | ~ l1_pre_topc(X2)
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2264,plain,
% 3.57/1.00      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
% 3.57/1.00      | v5_pre_topc(X0,sK0,X1)
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.57/1.00      | ~ v2_pre_topc(X1)
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(X1)
% 3.57/1.00      | ~ l1_pre_topc(sK0)
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_28]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2604,plain,
% 3.57/1.00      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.57/1.00      | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.57/1.00      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.57/1.00      | ~ l1_pre_topc(sK0)
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_2264]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3844,plain,
% 3.57/1.00      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.57/1.00      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.57/1.00      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.57/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.57/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.57/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.57/1.00      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.57/1.00      | ~ l1_pre_topc(sK0)
% 3.57/1.00      | ~ v1_funct_1(sK3) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_2604]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3845,plain,
% 3.57/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.57/1.00      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.57/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.57/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.57/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.57/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_3844]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_5306,plain,
% 3.57/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_5020,c_45,c_46,c_47,c_48,c_52,c_53,c_54,c_1904,c_1835,
% 3.57/1.00                 c_1832,c_1891,c_2129,c_2163,c_2300,c_3355,c_3418,c_3845]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_5307,plain,
% 3.57/1.00      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 3.57/1.00      inference(renaming,[status(thm)],[c_5306]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_5310,plain,
% 3.57/1.00      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_5307,c_45,c_46,c_47,c_48,c_52,c_53,c_54,c_1835,c_1832,
% 3.57/1.00                 c_1891,c_2129,c_2163,c_2300,c_3418,c_3845]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7732,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_7711,c_5310]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7766,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_7732,c_3]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_8125,plain,
% 3.57/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.57/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7766]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_8,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.57/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1802,plain,
% 3.57/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.57/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3054,plain,
% 3.57/1.00      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1784,c_1802]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7735,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_7711,c_3054]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7749,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_7735,c_3]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3053,plain,
% 3.57/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1804,c_1802]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_0,plain,
% 3.57/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.57/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1806,plain,
% 3.57/1.00      ( X0 = X1
% 3.57/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.57/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4898,plain,
% 3.57/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_3053,c_1806]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_8861,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | sK3 = k1_xboole_0 ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_7749,c_4898]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_5316,plain,
% 3.57/1.00      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1803,c_5310]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7731,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_7711,c_5316]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7773,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_7731,c_3]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_9828,plain,
% 3.57/1.00      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_7773,c_7744,c_7766]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_9829,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.57/1.00      inference(renaming,[status(thm)],[c_9828]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_9835,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_7711,c_9829]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4900,plain,
% 3.57/1.00      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
% 3.57/1.00      | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK3) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_3054,c_1806]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7733,plain,
% 3.57/1.00      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0),sK3) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_7711,c_4900]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7759,plain,
% 3.57/1.00      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_7733,c_3]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2919,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2920,plain,
% 3.57/1.00      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 3.57/1.00      | r1_tarski(X0,sK3) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_2919]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2922,plain,
% 3.57/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 3.57/1.00      | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_2920]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4508,plain,
% 3.57/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4511,plain,
% 3.57/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_4508]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_9918,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3 ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_7759,c_2922,c_4511]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_9919,plain,
% 3.57/1.00      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(renaming,[status(thm)],[c_9918]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f107]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1805,plain,
% 3.57/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4079,plain,
% 3.57/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.57/1.00      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1803,c_1800]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_5498,plain,
% 3.57/1.00      ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1805,c_4079]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_9926,plain,
% 3.57/1.00      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 3.57/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_9919,c_5498]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_10068,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(light_normalisation,[status(thm)],[c_9926,c_4080]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_10603,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_7711,c_10068]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_10655,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.57/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_10603,c_3,c_10]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1788,plain,
% 3.57/1.00      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 3.57/1.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 3.57/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.57/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 3.57/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.57/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 3.57/1.00      | v2_pre_topc(X1) != iProver_top
% 3.57/1.00      | v2_pre_topc(X2) != iProver_top
% 3.57/1.00      | l1_pre_topc(X1) != iProver_top
% 3.57/1.00      | l1_pre_topc(X2) != iProver_top
% 3.57/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4774,plain,
% 3.57/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.57/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.57/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.57/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.57/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.57/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1784,c_1788]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2131,plain,
% 3.57/1.00      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.57/1.00      | ~ l1_pre_topc(sK0) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2132,plain,
% 3.57/1.00      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 3.57/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_2131]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2165,plain,
% 3.57/1.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(sK0) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_27]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2166,plain,
% 3.57/1.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.57/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_2165]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2303,plain,
% 3.57/1.00      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.57/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2304,plain,
% 3.57/1.00      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.57/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_2303]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2274,plain,
% 3.57/1.00      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
% 3.57/1.00      | ~ v5_pre_topc(X0,sK0,X1)
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.57/1.00      | ~ v2_pre_topc(X1)
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(X1)
% 3.57/1.00      | ~ l1_pre_topc(sK0)
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_29]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2634,plain,
% 3.57/1.00      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.57/1.00      | ~ v5_pre_topc(X0,sK0,sK1)
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.57/1.00      | ~ v2_pre_topc(sK1)
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(sK1)
% 3.57/1.00      | ~ l1_pre_topc(sK0)
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_2274]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3330,plain,
% 3.57/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.57/1.00      | ~ v5_pre_topc(sK3,sK0,sK1)
% 3.57/1.00      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 3.57/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.57/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 3.57/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.57/1.00      | ~ v2_pre_topc(sK1)
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(sK1)
% 3.57/1.00      | ~ l1_pre_topc(sK0)
% 3.57/1.00      | ~ v1_funct_1(sK3) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_2634]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3331,plain,
% 3.57/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 3.57/1.00      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.57/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.57/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.57/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_3330]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3963,plain,
% 3.57/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.57/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.57/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.57/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.57/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.57/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1784,c_1787]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2594,plain,
% 3.57/1.00      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.57/1.00      | v5_pre_topc(X0,sK0,sK1)
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 3.57/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.57/1.00      | ~ v2_pre_topc(sK1)
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(sK1)
% 3.57/1.00      | ~ l1_pre_topc(sK0)
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_2264]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3306,plain,
% 3.57/1.00      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.57/1.00      | v5_pre_topc(sK3,sK0,sK1)
% 3.57/1.00      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 3.57/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.57/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 3.57/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.57/1.00      | ~ v2_pre_topc(sK1)
% 3.57/1.00      | ~ v2_pre_topc(sK0)
% 3.57/1.00      | ~ l1_pre_topc(sK1)
% 3.57/1.00      | ~ l1_pre_topc(sK0)
% 3.57/1.00      | ~ v1_funct_1(sK3) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_2594]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3307,plain,
% 3.57/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.57/1.00      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.57/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.57/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.57/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.57/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_3306]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4426,plain,
% 3.57/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_3963,c_45,c_46,c_47,c_48,c_52,c_53,c_1904,c_1835,c_1832,
% 3.57/1.00                 c_2132,c_2166,c_2304,c_3307]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4427,plain,
% 3.57/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.57/1.00      inference(renaming,[status(thm)],[c_4426]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4932,plain,
% 3.57/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_4774,c_45,c_46,c_47,c_48,c_52,c_53,c_1835,c_1832,c_1891,
% 3.57/1.00                 c_2132,c_2166,c_2304,c_3331,c_4427]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4933,plain,
% 3.57/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.57/1.00      inference(renaming,[status(thm)],[c_4932]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_11051,plain,
% 3.57/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_10655,c_4933]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1783,plain,
% 3.57/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_11057,plain,
% 3.57/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.57/1.00      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_10655,c_1783]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6067,plain,
% 3.57/1.00      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = u1_struct_0(sK0)
% 3.57/1.00      | u1_struct_0(sK1) = k1_xboole_0
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1835,c_1794]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4081,plain,
% 3.57/1.00      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1835,c_1800]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6077,plain,
% 3.57/1.00      ( u1_struct_0(sK1) = k1_xboole_0
% 3.57/1.00      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 3.57/1.00      inference(light_normalisation,[status(thm)],[c_6067,c_4081]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6188,plain,
% 3.57/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3) | u1_struct_0(sK1) = k1_xboole_0 ),
% 3.57/1.00      inference(global_propositional_subsumption,[status(thm)],[c_6077,c_1832]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6189,plain,
% 3.57/1.00      ( u1_struct_0(sK1) = k1_xboole_0 | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(renaming,[status(thm)],[c_6188]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3055,plain,
% 3.57/1.00      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1835,c_1802]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4901,plain,
% 3.57/1.00      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 3.57/1.00      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK3) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_3055,c_1806]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6208,plain,
% 3.57/1.00      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 3.57/1.00      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.57/1.00      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),sK3) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_6189,c_4901]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6296,plain,
% 3.57/1.00      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 3.57/1.00      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.57/1.00      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_6208,c_3]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6938,plain,
% 3.57/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.57/1.00      | k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3 ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_6296,c_2922,c_4511]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6939,plain,
% 3.57/1.00      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 3.57/1.00      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(renaming,[status(thm)],[c_6938]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6944,plain,
% 3.57/1.00      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 3.57/1.00      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_6939,c_5498]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6986,plain,
% 3.57/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.57/1.00      | k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(light_normalisation,[status(thm)],[c_6944,c_4081]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7258,plain,
% 3.57/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.57/1.00      | k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_6189,c_6986]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7281,plain,
% 3.57/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3) | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_7258,c_3,c_10]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_11056,plain,
% 3.57/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_10655,c_1784]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_8374,plain,
% 3.57/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_7281,c_5310]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_12039,plain,
% 3.57/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_11056,c_8374]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_12105,plain,
% 3.57/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.57/1.00      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_7281,c_12039]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_12114,plain,
% 3.57/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_11051,c_11057,c_12105]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6221,plain,
% 3.57/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_6189,c_1832]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_12145,plain,
% 3.57/1.00      ( u1_struct_0(sK0) = k1_xboole_0
% 3.57/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) = iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_12114,c_6221]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_13617,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_10857,c_123,c_2051,c_4110,c_5414,c_7711,c_8122,c_8125,
% 3.57/1.00                 c_8861,c_9835,c_12145]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_13619,plain,
% 3.57/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0 ),
% 3.57/1.00      inference(light_normalisation,[status(thm)],[c_13617,c_12114]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_13630,plain,
% 3.57/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_13619,c_1784]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_13635,plain,
% 3.57/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_13630,c_4]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_15,plain,
% 3.57/1.00      ( v1_funct_2(X0,X1,X2)
% 3.57/1.00      | ~ v1_partfun1(X0,X1)
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_13,plain,
% 3.57/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.57/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_23,plain,
% 3.57/1.00      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.57/1.00      | ~ v4_relat_1(X0,k1_relat_1(X0))
% 3.57/1.00      | ~ v1_relat_1(X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_535,plain,
% 3.57/1.00      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.57/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.57/1.00      | ~ v1_relat_1(X0)
% 3.57/1.00      | X0 != X1
% 3.57/1.00      | k1_relat_1(X0) != X2 ),
% 3.57/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_536,plain,
% 3.57/1.00      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.57/1.00      | ~ v1_relat_1(X0) ),
% 3.57/1.00      inference(unflattening,[status(thm)],[c_535]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_12,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_546,plain,
% 3.57/1.00      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) ),
% 3.57/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_536,c_12]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_581,plain,
% 3.57/1.00      ( v1_funct_2(X0,X1,X2)
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X3),X4)))
% 3.57/1.00      | ~ v1_funct_1(X0)
% 3.57/1.00      | X3 != X0
% 3.57/1.00      | k1_relat_1(X3) != X1 ),
% 3.57/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_546]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_582,plain,
% 3.57/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
% 3.57/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.57/1.00      | ~ v1_funct_1(X0) ),
% 3.57/1.00      inference(unflattening,[status(thm)],[c_581]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1773,plain,
% 3.57/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 3.57/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) != iProver_top
% 3.57/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2))) != iProver_top
% 3.57/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_12325,plain,
% 3.57/1.00      ( v1_funct_2(sK3,k1_relat_1(sK3),X0) = iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1))) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 3.57/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_12114,c_1773]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_12330,plain,
% 3.57/1.00      ( v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.57/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.57/1.00      inference(light_normalisation,[status(thm)],[c_12325,c_4,c_12114]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_12331,plain,
% 3.57/1.00      ( v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.57/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_12330,c_4]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_12560,plain,
% 3.57/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.57/1.00      | v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top ),
% 3.57/1.00      inference(global_propositional_subsumption,[status(thm)],[c_12331,c_52]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_12561,plain,
% 3.57/1.00      ( v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.57/1.00      inference(renaming,[status(thm)],[c_12560]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_14479,plain,
% 3.57/1.00      ( v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_13635,c_12561]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4938,plain,
% 3.57/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1803,c_4933]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_13625,plain,
% 3.57/1.00      ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) != iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_13619,c_4938]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_13661,plain,
% 3.57/1.00      ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_13625,c_4]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_13626,plain,
% 3.57/1.00      ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_13619,c_4933]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_13656,plain,
% 3.57/1.00      ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
% 3.57/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.57/1.00      inference(demodulation,[status(thm)],[c_13626,c_4]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_14939,plain,
% 3.57/1.00      ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_13661,c_13635,c_13656]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_15176,plain,
% 3.57/1.00      ( $false ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_14479,c_14939]) ).
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.57/1.00  
% 3.57/1.00  ------                               Statistics
% 3.57/1.00  
% 3.57/1.00  ------ General
% 3.57/1.00  
% 3.57/1.00  abstr_ref_over_cycles:                  0
% 3.57/1.00  abstr_ref_under_cycles:                 0
% 3.57/1.00  gc_basic_clause_elim:                   0
% 3.57/1.00  forced_gc_time:                         0
% 3.57/1.00  parsing_time:                           0.01
% 3.57/1.00  unif_index_cands_time:                  0.
% 3.57/1.00  unif_index_add_time:                    0.
% 3.57/1.00  orderings_time:                         0.
% 3.57/1.00  out_proof_time:                         0.019
% 3.57/1.00  total_time:                             0.486
% 3.57/1.00  num_of_symbols:                         54
% 3.57/1.00  num_of_terms:                           10143
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing
% 3.57/1.00  
% 3.57/1.00  num_of_splits:                          0
% 3.57/1.00  num_of_split_atoms:                     0
% 3.57/1.00  num_of_reused_defs:                     0
% 3.57/1.00  num_eq_ax_congr_red:                    17
% 3.57/1.00  num_of_sem_filtered_clauses:            1
% 3.57/1.00  num_of_subtypes:                        0
% 3.57/1.00  monotx_restored_types:                  0
% 3.57/1.00  sat_num_of_epr_types:                   0
% 3.57/1.00  sat_num_of_non_cyclic_types:            0
% 3.57/1.00  sat_guarded_non_collapsed_types:        0
% 3.57/1.00  num_pure_diseq_elim:                    0
% 3.57/1.00  simp_replaced_by:                       0
% 3.57/1.00  res_preprocessed:                       196
% 3.57/1.00  prep_upred:                             0
% 3.57/1.00  prep_unflattend:                        8
% 3.57/1.00  smt_new_axioms:                         0
% 3.57/1.00  pred_elim_cands:                        8
% 3.57/1.00  pred_elim:                              2
% 3.57/1.00  pred_elim_cl:                           3
% 3.57/1.00  pred_elim_cycles:                       5
% 3.57/1.00  merged_defs:                            16
% 3.57/1.00  merged_defs_ncl:                        0
% 3.57/1.00  bin_hyper_res:                          17
% 3.57/1.00  prep_cycles:                            4
% 3.57/1.00  pred_elim_time:                         0.004
% 3.57/1.00  splitting_time:                         0.
% 3.57/1.00  sem_filter_time:                        0.
% 3.57/1.00  monotx_time:                            0.001
% 3.57/1.00  subtype_inf_time:                       0.
% 3.57/1.00  
% 3.57/1.00  ------ Problem properties
% 3.57/1.00  
% 3.57/1.00  clauses:                                40
% 3.57/1.00  conjectures:                            13
% 3.57/1.00  epr:                                    10
% 3.57/1.00  horn:                                   34
% 3.57/1.00  ground:                                 15
% 3.57/1.00  unary:                                  17
% 3.57/1.00  binary:                                 8
% 3.57/1.00  lits:                                   115
% 3.57/1.00  lits_eq:                                19
% 3.57/1.00  fd_pure:                                0
% 3.57/1.00  fd_pseudo:                              0
% 3.57/1.00  fd_cond:                                4
% 3.57/1.00  fd_pseudo_cond:                         1
% 3.57/1.00  ac_symbols:                             0
% 3.57/1.00  
% 3.57/1.00  ------ Propositional Solver
% 3.57/1.00  
% 3.57/1.00  prop_solver_calls:                      27
% 3.57/1.00  prop_fast_solver_calls:                 1844
% 3.57/1.00  smt_solver_calls:                       0
% 3.57/1.00  smt_fast_solver_calls:                  0
% 3.57/1.00  prop_num_of_clauses:                    4271
% 3.57/1.00  prop_preprocess_simplified:             11093
% 3.57/1.00  prop_fo_subsumed:                       88
% 3.57/1.00  prop_solver_time:                       0.
% 3.57/1.00  smt_solver_time:                        0.
% 3.57/1.00  smt_fast_solver_time:                   0.
% 3.57/1.00  prop_fast_solver_time:                  0.
% 3.57/1.00  prop_unsat_core_time:                   0.
% 3.57/1.00  
% 3.57/1.00  ------ QBF
% 3.57/1.00  
% 3.57/1.00  qbf_q_res:                              0
% 3.57/1.00  qbf_num_tautologies:                    0
% 3.57/1.00  qbf_prep_cycles:                        0
% 3.57/1.00  
% 3.57/1.00  ------ BMC1
% 3.57/1.00  
% 3.57/1.00  bmc1_current_bound:                     -1
% 3.57/1.00  bmc1_last_solved_bound:                 -1
% 3.57/1.00  bmc1_unsat_core_size:                   -1
% 3.57/1.00  bmc1_unsat_core_parents_size:           -1
% 3.57/1.00  bmc1_merge_next_fun:                    0
% 3.57/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.57/1.00  
% 3.57/1.00  ------ Instantiation
% 3.57/1.00  
% 3.57/1.00  inst_num_of_clauses:                    1305
% 3.57/1.00  inst_num_in_passive:                    358
% 3.57/1.00  inst_num_in_active:                     608
% 3.57/1.00  inst_num_in_unprocessed:                343
% 3.57/1.00  inst_num_of_loops:                      770
% 3.57/1.00  inst_num_of_learning_restarts:          0
% 3.57/1.00  inst_num_moves_active_passive:          161
% 3.57/1.00  inst_lit_activity:                      0
% 3.57/1.00  inst_lit_activity_moves:                0
% 3.57/1.00  inst_num_tautologies:                   0
% 3.57/1.00  inst_num_prop_implied:                  0
% 3.57/1.00  inst_num_existing_simplified:           0
% 3.57/1.00  inst_num_eq_res_simplified:             0
% 3.57/1.00  inst_num_child_elim:                    0
% 3.57/1.00  inst_num_of_dismatching_blockings:      388
% 3.57/1.00  inst_num_of_non_proper_insts:           1323
% 3.57/1.00  inst_num_of_duplicates:                 0
% 3.57/1.00  inst_inst_num_from_inst_to_res:         0
% 3.57/1.00  inst_dismatching_checking_time:         0.
% 3.57/1.00  
% 3.57/1.00  ------ Resolution
% 3.57/1.00  
% 3.57/1.00  res_num_of_clauses:                     0
% 3.57/1.00  res_num_in_passive:                     0
% 3.57/1.00  res_num_in_active:                      0
% 3.57/1.00  res_num_of_loops:                       200
% 3.57/1.00  res_forward_subset_subsumed:            51
% 3.57/1.00  res_backward_subset_subsumed:           10
% 3.57/1.00  res_forward_subsumed:                   0
% 3.57/1.00  res_backward_subsumed:                  0
% 3.57/1.00  res_forward_subsumption_resolution:     1
% 3.57/1.00  res_backward_subsumption_resolution:    0
% 3.57/1.00  res_clause_to_clause_subsumption:       877
% 3.57/1.00  res_orphan_elimination:                 0
% 3.57/1.00  res_tautology_del:                      69
% 3.57/1.00  res_num_eq_res_simplified:              0
% 3.57/1.00  res_num_sel_changes:                    0
% 3.57/1.00  res_moves_from_active_to_pass:          0
% 3.57/1.00  
% 3.57/1.00  ------ Superposition
% 3.57/1.00  
% 3.57/1.00  sup_time_total:                         0.
% 3.57/1.00  sup_time_generating:                    0.
% 3.57/1.00  sup_time_sim_full:                      0.
% 3.57/1.00  sup_time_sim_immed:                     0.
% 3.57/1.00  
% 3.57/1.00  sup_num_of_clauses:                     253
% 3.57/1.00  sup_num_in_active:                      89
% 3.57/1.00  sup_num_in_passive:                     164
% 3.57/1.00  sup_num_of_loops:                       152
% 3.57/1.00  sup_fw_superposition:                   189
% 3.57/1.00  sup_bw_superposition:                   319
% 3.57/1.00  sup_immediate_simplified:               189
% 3.57/1.00  sup_given_eliminated:                   2
% 3.57/1.00  comparisons_done:                       0
% 3.57/1.00  comparisons_avoided:                    12
% 3.57/1.00  
% 3.57/1.00  ------ Simplifications
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  sim_fw_subset_subsumed:                 74
% 3.57/1.00  sim_bw_subset_subsumed:                 78
% 3.57/1.00  sim_fw_subsumed:                        24
% 3.57/1.00  sim_bw_subsumed:                        9
% 3.57/1.00  sim_fw_subsumption_res:                 3
% 3.57/1.00  sim_bw_subsumption_res:                 0
% 3.57/1.00  sim_tautology_del:                      5
% 3.57/1.00  sim_eq_tautology_del:                   11
% 3.57/1.00  sim_eq_res_simp:                        1
% 3.57/1.00  sim_fw_demodulated:                     70
% 3.57/1.00  sim_bw_demodulated:                     47
% 3.57/1.00  sim_light_normalised:                   70
% 3.57/1.00  sim_joinable_taut:                      0
% 3.57/1.00  sim_joinable_simp:                      0
% 3.57/1.00  sim_ac_normalised:                      0
% 3.57/1.00  sim_smt_subsumption:                    0
% 3.57/1.00  
%------------------------------------------------------------------------------
