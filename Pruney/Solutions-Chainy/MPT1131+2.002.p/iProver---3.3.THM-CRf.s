%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:46 EST 2020

% Result     : Theorem 27.35s
% Output     : CNFRefutation 27.35s
% Verified   : 
% Statistics : Number of formulae       :  278 (3850 expanded)
%              Number of clauses        :  186 (1324 expanded)
%              Number of leaves         :   27 ( 729 expanded)
%              Depth                    :   39
%              Number of atoms          : 1327 (23949 expanded)
%              Number of equality atoms :  502 (4025 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
            | ~ v5_pre_topc(X2,X0,X1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
            | v5_pre_topc(X2,X0,X1) )
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
          & v1_funct_1(X3) )
     => ( ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
          | v5_pre_topc(X2,X0,X1) )
        & sK8 = X2
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                | v5_pre_topc(X2,X0,X1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
              | ~ v5_pre_topc(sK7,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
              | v5_pre_topc(sK7,X0,X1) )
            & sK7 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK6)
                  | ~ v5_pre_topc(X2,X0,sK6) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK6)
                  | v5_pre_topc(X2,X0,sK6) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK6))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK6))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK6))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK6)
        & v2_pre_topc(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1)
                    | ~ v5_pre_topc(X2,sK5,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1)
                    | v5_pre_topc(X2,sK5,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
      | ~ v5_pre_topc(sK7,sK5,sK6) )
    & ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
      | v5_pre_topc(sK7,sK5,sK6) )
    & sK7 = sK8
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    & v1_funct_1(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f58,f62,f61,f60,f59])).

fof(f105,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f109,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f63])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0)
        & v4_pre_topc(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0)
                    & v4_pre_topc(sK1(X0,X1,X2),X1)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f112,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f33,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f33])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
        & r1_tarski(sK4(X0),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
            & r1_tarski(sK4(X0),u1_pre_topc(X0))
            & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f80,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f90,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f89,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f88,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f102,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f106,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f63])).

fof(f104,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f63])).

fof(f111,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v5_pre_topc(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f110,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f113,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f108,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f107,plain,(
    v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f63])).

fof(f103,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3202,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_53207,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(sK6),sK7,sK1(X2,sK6,sK7)),X2)
    | X2 != X1
    | k8_relset_1(u1_struct_0(X2),u1_struct_0(sK6),sK7,sK1(X2,sK6,sK7)) != X0 ),
    inference(instantiation,[status(thm)],[c_3202])).

cnf(c_71141,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK6),sK7,sK1(X0,sK6,sK7)),X0)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
    | X0 != sK5
    | k8_relset_1(u1_struct_0(X0),u1_struct_0(sK6),sK7,sK1(X0,sK6,sK7)) != k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_53207])).

cnf(c_71154,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
    | k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)) != k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_71141])).

cnf(c_3198,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k8_relset_1(X0,X2,X6,X4) = k8_relset_1(X1,X3,X6,X5) ),
    theory(equality)).

cnf(c_52347,plain,
    ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)) = k8_relset_1(X0,X1,sK7,X2)
    | sK1(sK5,sK6,sK7) != X2
    | u1_struct_0(sK6) != X1
    | u1_struct_0(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_3198])).

cnf(c_53092,plain,
    ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)) = k8_relset_1(X0,u1_struct_0(sK6),sK7,X1)
    | sK1(sK5,sK6,sK7) != X1
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_52347])).

cnf(c_54526,plain,
    ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(sK6),sK7,X1)
    | sK1(sK5,sK6,sK7) != X1
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_53092])).

cnf(c_58315,plain,
    ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7))
    | sK1(sK5,sK6,sK7) != sK1(sK5,sK6,sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_54526])).

cnf(c_67293,plain,
    ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)) = k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7))
    | sK1(sK5,sK6,sK7) != sK1(sK5,sK6,sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(instantiation,[status(thm)],[c_58315])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_61024,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_32,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_5812,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v4_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_7282,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0),X1,X2),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0),X1,X2),sK5)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_5812])).

cnf(c_10168,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0),sK7,X1),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0),sK7,X1),sK5)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0),sK7,X1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_7282])).

cnf(c_47314,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_10168])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_4240,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_37,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_4282,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4240,c_37])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4271,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) != iProver_top
    | v4_pre_topc(X3,X2) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4275,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_47,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_4234,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_4278,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4277,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_29,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_4251,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4276,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6624,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4251,c_4276])).

cnf(c_21,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4259,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4258,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6118,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4277,c_4258])).

cnf(c_6283,plain,
    ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4259,c_6118])).

cnf(c_6290,plain,
    ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4278,c_6283])).

cnf(c_27,plain,
    ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_4253,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6827,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | r1_tarski(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4277,c_4253])).

cnf(c_8182,plain,
    ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4278,c_6827])).

cnf(c_8272,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6290,c_8182])).

cnf(c_26,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_84,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4255,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4256,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5028,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4255,c_4256])).

cnf(c_8494,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8272,c_84,c_5028])).

cnf(c_8495,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8494])).

cnf(c_8500,plain,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X0)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8495,c_4276])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4279,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8613,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8500,c_4279])).

cnf(c_8623,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0)
    | v3_pre_topc(u1_struct_0(X0),X0) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6624,c_8613])).

cnf(c_8707,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8623,c_6290])).

cnf(c_8713,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4277,c_8707])).

cnf(c_8797,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0)
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4278,c_8713])).

cnf(c_8855,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4234,c_8797])).

cnf(c_48,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_49,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_8801,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8797])).

cnf(c_9186,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8855,c_48,c_49,c_8801])).

cnf(c_34,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4246,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4274,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7269,plain,
    ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2),X0,sK1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2,X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2),X0,sK1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2,X0)),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4246,c_4274])).

cnf(c_20000,plain,
    ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9186,c_7269])).

cnf(c_20039,plain,
    ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20000,c_9186])).

cnf(c_9229,plain,
    ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9186,c_4274])).

cnf(c_9293,plain,
    ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9229,c_9186])).

cnf(c_87,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_89,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_4378,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_4379,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4378])).

cnf(c_19879,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9293,c_49,c_89,c_4379])).

cnf(c_19880,plain,
    ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_19879])).

cnf(c_19885,plain,
    ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4246,c_19880])).

cnf(c_24710,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),sK5) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20039,c_48,c_49,c_19885])).

cnf(c_24711,plain,
    ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_24710])).

cnf(c_24717,plain,
    ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4275,c_24711])).

cnf(c_26513,plain,
    ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v5_pre_topc(X0,sK5,X1) != iProver_top
    | v4_pre_topc(sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4271,c_24717])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v4_pre_topc(sK1(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4273,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | v4_pre_topc(sK1(X1,X2,X0),X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9231,plain,
    ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v4_pre_topc(sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9186,c_4273])).

cnf(c_9291,plain,
    ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v4_pre_topc(sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9231,c_9186])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4272,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9230,plain,
    ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9186,c_4272])).

cnf(c_9292,plain,
    ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9230,c_9186])).

cnf(c_42493,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v5_pre_topc(X0,sK5,X1) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26513,c_49,c_89,c_4379,c_9291,c_9292])).

cnf(c_42494,plain,
    ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
    | v5_pre_topc(X0,sK5,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_42493])).

cnf(c_42501,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
    | v5_pre_topc(sK8,sK5,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4282,c_42494])).

cnf(c_44,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_51,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_55,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_4239,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_4281,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4239,c_37])).

cnf(c_35,negated_conjecture,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_4245,plain,
    ( v5_pre_topc(sK7,sK5,sK6) != iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4284,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top
    | v5_pre_topc(sK8,sK5,sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4245,c_37])).

cnf(c_42629,plain,
    ( v5_pre_topc(sK8,sK5,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42501,c_51,c_55,c_4281,c_4284])).

cnf(c_42631,plain,
    ( ~ v5_pre_topc(sK8,sK5,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_42629])).

cnf(c_3203,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_11605,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != X1
    | u1_struct_0(sK6) != X2
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_3203])).

cnf(c_17578,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v1_funct_2(sK8,X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != X0
    | u1_struct_0(sK6) != X1
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_11605])).

cnf(c_22780,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v1_funct_2(sK8,X0,u1_struct_0(sK6))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != X0
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_17578])).

cnf(c_36740,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_22780])).

cnf(c_11546,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v5_pre_topc(sK7,X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,X2),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_16445,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(sK6))
    | ~ v5_pre_topc(sK7,X0,sK6)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),X0)
    | ~ v4_pre_topc(sK1(sK5,sK6,sK7),sK6)
    | ~ m1_subset_1(sK1(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_11546])).

cnf(c_36193,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v4_pre_topc(sK1(sK5,sK6,sK7),sK6)
    | ~ m1_subset_1(sK1(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_16445])).

cnf(c_3200,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_6867,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(sK7,X3,sK6)
    | X3 != X1
    | sK7 != X0
    | sK6 != X2 ),
    inference(instantiation,[status(thm)],[c_3200])).

cnf(c_10560,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != X1
    | sK7 != X0
    | sK6 != X2 ),
    inference(instantiation,[status(thm)],[c_6867])).

cnf(c_12627,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v5_pre_topc(sK8,X0,X1)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != X0
    | sK7 != sK8
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_10560])).

cnf(c_16164,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v5_pre_topc(sK8,X0,sK6)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != X0
    | sK7 != sK8
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_12627])).

cnf(c_23026,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
    | sK7 != sK8
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_16164])).

cnf(c_3194,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6216,plain,
    ( X0 != X1
    | u1_struct_0(sK5) != X1
    | u1_struct_0(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_3194])).

cnf(c_8531,plain,
    ( X0 != u1_struct_0(sK5)
    | u1_struct_0(sK5) = X0
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_6216])).

cnf(c_11956,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(sK5) = u1_struct_0(X0)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_8531])).

cnf(c_20213,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != u1_struct_0(sK5)
    | u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_11956])).

cnf(c_4590,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(sK8,X3,sK6)
    | X3 != X1
    | sK6 != X2
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_3200])).

cnf(c_6932,plain,
    ( ~ v5_pre_topc(X0,X1,sK6)
    | v5_pre_topc(sK8,X2,sK6)
    | X2 != X1
    | sK6 != sK6
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_4590])).

cnf(c_18153,plain,
    ( ~ v5_pre_topc(sK7,X0,sK6)
    | v5_pre_topc(sK8,X1,sK6)
    | X1 != X0
    | sK6 != sK6
    | sK8 != sK7 ),
    inference(instantiation,[status(thm)],[c_6932])).

cnf(c_18155,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK8,sK5,sK6)
    | sK6 != sK6
    | sK5 != sK5
    | sK8 != sK7 ),
    inference(instantiation,[status(thm)],[c_18153])).

cnf(c_6902,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = X1
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6624,c_4279])).

cnf(c_13350,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),X0) != iProver_top
    | v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),X1) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6624,c_6902])).

cnf(c_13362,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK5) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13350])).

cnf(c_3193,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_11652,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_3193])).

cnf(c_3197,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6748,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | X1 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))
    | X0 != sK8 ),
    inference(instantiation,[status(thm)],[c_3197])).

cnf(c_7428,plain,
    ( m1_subset_1(sK7,X0)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | X0 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_6748])).

cnf(c_10710,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_7428])).

cnf(c_8314,plain,
    ( r1_tarski(sK1(sK5,sK6,sK7),sK1(sK5,sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_8274,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8272])).

cnf(c_5887,plain,
    ( ~ r1_tarski(X0,sK1(sK5,sK6,sK7))
    | ~ r1_tarski(sK1(sK5,sK6,sK7),X0)
    | sK1(sK5,sK6,sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7323,plain,
    ( ~ r1_tarski(sK1(sK5,sK6,sK7),sK1(sK5,sK6,sK7))
    | sK1(sK5,sK6,sK7) = sK1(sK5,sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_5887])).

cnf(c_28,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_4252,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6811,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | r1_tarski(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4277,c_4252])).

cnf(c_7095,plain,
    ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),X0) = iProver_top
    | v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4278,c_6811])).

cnf(c_7104,plain,
    ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6290,c_7095])).

cnf(c_7106,plain,
    ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK5) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7104])).

cnf(c_5963,plain,
    ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5181,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK6))
    | ~ r1_tarski(u1_struct_0(sK6),X0)
    | u1_struct_0(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5606,plain,
    ( ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6))
    | u1_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_5181])).

cnf(c_4604,plain,
    ( X0 != X1
    | X0 = sK7
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_3194])).

cnf(c_5097,plain,
    ( X0 = sK7
    | X0 != sK8
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_4604])).

cnf(c_5300,plain,
    ( sK7 != sK8
    | sK8 = sK7
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_5097])).

cnf(c_5055,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_3193])).

cnf(c_4955,plain,
    ( r1_tarski(sK8,sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4564,plain,
    ( ~ r1_tarski(X0,sK8)
    | ~ r1_tarski(sK8,X0)
    | X0 = sK8 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4846,plain,
    ( ~ r1_tarski(sK8,sK8)
    | sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_4564])).

cnf(c_4526,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4385,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4452,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_4385])).

cnf(c_4342,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | v5_pre_topc(sK7,sK5,sK6)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4343,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | v5_pre_topc(sK7,sK5,sK6)
    | m1_subset_1(sK1(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4344,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | v5_pre_topc(sK7,sK5,sK6)
    | v4_pre_topc(sK1(sK5,sK6,sK7),sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_36,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_4244,plain,
    ( v5_pre_topc(sK7,sK5,sK6) = iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4283,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
    | v5_pre_topc(sK8,sK5,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4244,c_37])).

cnf(c_4312,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK8,sK5,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4283])).

cnf(c_3201,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_3219,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3201])).

cnf(c_155,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_151,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_88,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_86,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f103])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_71154,c_67293,c_61024,c_47314,c_42631,c_36740,c_36193,c_23026,c_20213,c_18155,c_13362,c_11652,c_10710,c_8801,c_8314,c_8274,c_7323,c_7106,c_5963,c_5606,c_5300,c_5055,c_4955,c_4846,c_4526,c_4452,c_4379,c_4378,c_4342,c_4343,c_4344,c_4312,c_3219,c_155,c_151,c_89,c_88,c_86,c_37,c_38,c_39,c_41,c_42,c_43,c_44,c_49,c_46,c_48,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:39:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.35/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.35/3.99  
% 27.35/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.35/3.99  
% 27.35/3.99  ------  iProver source info
% 27.35/3.99  
% 27.35/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.35/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.35/3.99  git: non_committed_changes: false
% 27.35/3.99  git: last_make_outside_of_git: false
% 27.35/3.99  
% 27.35/3.99  ------ 
% 27.35/3.99  
% 27.35/3.99  ------ Input Options
% 27.35/3.99  
% 27.35/3.99  --out_options                           all
% 27.35/3.99  --tptp_safe_out                         true
% 27.35/3.99  --problem_path                          ""
% 27.35/3.99  --include_path                          ""
% 27.35/3.99  --clausifier                            res/vclausify_rel
% 27.35/3.99  --clausifier_options                    ""
% 27.35/3.99  --stdin                                 false
% 27.35/3.99  --stats_out                             all
% 27.35/3.99  
% 27.35/3.99  ------ General Options
% 27.35/3.99  
% 27.35/3.99  --fof                                   false
% 27.35/3.99  --time_out_real                         305.
% 27.35/3.99  --time_out_virtual                      -1.
% 27.35/3.99  --symbol_type_check                     false
% 27.35/3.99  --clausify_out                          false
% 27.35/3.99  --sig_cnt_out                           false
% 27.35/3.99  --trig_cnt_out                          false
% 27.35/3.99  --trig_cnt_out_tolerance                1.
% 27.35/3.99  --trig_cnt_out_sk_spl                   false
% 27.35/3.99  --abstr_cl_out                          false
% 27.35/3.99  
% 27.35/3.99  ------ Global Options
% 27.35/3.99  
% 27.35/3.99  --schedule                              default
% 27.35/3.99  --add_important_lit                     false
% 27.35/3.99  --prop_solver_per_cl                    1000
% 27.35/3.99  --min_unsat_core                        false
% 27.35/3.99  --soft_assumptions                      false
% 27.35/3.99  --soft_lemma_size                       3
% 27.35/3.99  --prop_impl_unit_size                   0
% 27.35/3.99  --prop_impl_unit                        []
% 27.35/3.99  --share_sel_clauses                     true
% 27.35/3.99  --reset_solvers                         false
% 27.35/3.99  --bc_imp_inh                            [conj_cone]
% 27.35/3.99  --conj_cone_tolerance                   3.
% 27.35/3.99  --extra_neg_conj                        none
% 27.35/3.99  --large_theory_mode                     true
% 27.35/3.99  --prolific_symb_bound                   200
% 27.35/3.99  --lt_threshold                          2000
% 27.35/3.99  --clause_weak_htbl                      true
% 27.35/3.99  --gc_record_bc_elim                     false
% 27.35/3.99  
% 27.35/3.99  ------ Preprocessing Options
% 27.35/3.99  
% 27.35/3.99  --preprocessing_flag                    true
% 27.35/3.99  --time_out_prep_mult                    0.1
% 27.35/3.99  --splitting_mode                        input
% 27.35/3.99  --splitting_grd                         true
% 27.35/3.99  --splitting_cvd                         false
% 27.35/3.99  --splitting_cvd_svl                     false
% 27.35/3.99  --splitting_nvd                         32
% 27.35/3.99  --sub_typing                            true
% 27.35/3.99  --prep_gs_sim                           true
% 27.35/3.99  --prep_unflatten                        true
% 27.35/3.99  --prep_res_sim                          true
% 27.35/3.99  --prep_upred                            true
% 27.35/3.99  --prep_sem_filter                       exhaustive
% 27.35/3.99  --prep_sem_filter_out                   false
% 27.35/3.99  --pred_elim                             true
% 27.35/3.99  --res_sim_input                         true
% 27.35/3.99  --eq_ax_congr_red                       true
% 27.35/3.99  --pure_diseq_elim                       true
% 27.35/3.99  --brand_transform                       false
% 27.35/3.99  --non_eq_to_eq                          false
% 27.35/3.99  --prep_def_merge                        true
% 27.35/3.99  --prep_def_merge_prop_impl              false
% 27.35/3.99  --prep_def_merge_mbd                    true
% 27.35/3.99  --prep_def_merge_tr_red                 false
% 27.35/3.99  --prep_def_merge_tr_cl                  false
% 27.35/3.99  --smt_preprocessing                     true
% 27.35/3.99  --smt_ac_axioms                         fast
% 27.35/3.99  --preprocessed_out                      false
% 27.35/3.99  --preprocessed_stats                    false
% 27.35/3.99  
% 27.35/3.99  ------ Abstraction refinement Options
% 27.35/3.99  
% 27.35/3.99  --abstr_ref                             []
% 27.35/3.99  --abstr_ref_prep                        false
% 27.35/3.99  --abstr_ref_until_sat                   false
% 27.35/3.99  --abstr_ref_sig_restrict                funpre
% 27.35/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.35/3.99  --abstr_ref_under                       []
% 27.35/3.99  
% 27.35/3.99  ------ SAT Options
% 27.35/3.99  
% 27.35/3.99  --sat_mode                              false
% 27.35/3.99  --sat_fm_restart_options                ""
% 27.35/3.99  --sat_gr_def                            false
% 27.35/3.99  --sat_epr_types                         true
% 27.35/3.99  --sat_non_cyclic_types                  false
% 27.35/3.99  --sat_finite_models                     false
% 27.35/3.99  --sat_fm_lemmas                         false
% 27.35/3.99  --sat_fm_prep                           false
% 27.35/3.99  --sat_fm_uc_incr                        true
% 27.35/3.99  --sat_out_model                         small
% 27.35/3.99  --sat_out_clauses                       false
% 27.35/3.99  
% 27.35/3.99  ------ QBF Options
% 27.35/3.99  
% 27.35/3.99  --qbf_mode                              false
% 27.35/3.99  --qbf_elim_univ                         false
% 27.35/3.99  --qbf_dom_inst                          none
% 27.35/3.99  --qbf_dom_pre_inst                      false
% 27.35/3.99  --qbf_sk_in                             false
% 27.35/3.99  --qbf_pred_elim                         true
% 27.35/3.99  --qbf_split                             512
% 27.35/3.99  
% 27.35/3.99  ------ BMC1 Options
% 27.35/3.99  
% 27.35/3.99  --bmc1_incremental                      false
% 27.35/3.99  --bmc1_axioms                           reachable_all
% 27.35/3.99  --bmc1_min_bound                        0
% 27.35/3.99  --bmc1_max_bound                        -1
% 27.35/3.99  --bmc1_max_bound_default                -1
% 27.35/3.99  --bmc1_symbol_reachability              true
% 27.35/3.99  --bmc1_property_lemmas                  false
% 27.35/3.99  --bmc1_k_induction                      false
% 27.35/3.99  --bmc1_non_equiv_states                 false
% 27.35/3.99  --bmc1_deadlock                         false
% 27.35/3.99  --bmc1_ucm                              false
% 27.35/3.99  --bmc1_add_unsat_core                   none
% 27.35/3.99  --bmc1_unsat_core_children              false
% 27.35/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.35/3.99  --bmc1_out_stat                         full
% 27.35/3.99  --bmc1_ground_init                      false
% 27.35/3.99  --bmc1_pre_inst_next_state              false
% 27.35/3.99  --bmc1_pre_inst_state                   false
% 27.35/3.99  --bmc1_pre_inst_reach_state             false
% 27.35/3.99  --bmc1_out_unsat_core                   false
% 27.35/3.99  --bmc1_aig_witness_out                  false
% 27.35/3.99  --bmc1_verbose                          false
% 27.35/3.99  --bmc1_dump_clauses_tptp                false
% 27.35/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.35/3.99  --bmc1_dump_file                        -
% 27.35/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.35/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.35/3.99  --bmc1_ucm_extend_mode                  1
% 27.35/3.99  --bmc1_ucm_init_mode                    2
% 27.35/3.99  --bmc1_ucm_cone_mode                    none
% 27.35/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.35/3.99  --bmc1_ucm_relax_model                  4
% 27.35/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.35/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.35/3.99  --bmc1_ucm_layered_model                none
% 27.35/3.99  --bmc1_ucm_max_lemma_size               10
% 27.35/3.99  
% 27.35/3.99  ------ AIG Options
% 27.35/3.99  
% 27.35/3.99  --aig_mode                              false
% 27.35/3.99  
% 27.35/3.99  ------ Instantiation Options
% 27.35/3.99  
% 27.35/3.99  --instantiation_flag                    true
% 27.35/3.99  --inst_sos_flag                         true
% 27.35/3.99  --inst_sos_phase                        true
% 27.35/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.35/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.35/3.99  --inst_lit_sel_side                     num_symb
% 27.35/3.99  --inst_solver_per_active                1400
% 27.35/3.99  --inst_solver_calls_frac                1.
% 27.35/3.99  --inst_passive_queue_type               priority_queues
% 27.35/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.35/3.99  --inst_passive_queues_freq              [25;2]
% 27.35/3.99  --inst_dismatching                      true
% 27.35/3.99  --inst_eager_unprocessed_to_passive     true
% 27.35/3.99  --inst_prop_sim_given                   true
% 27.35/3.99  --inst_prop_sim_new                     false
% 27.35/3.99  --inst_subs_new                         false
% 27.35/3.99  --inst_eq_res_simp                      false
% 27.35/3.99  --inst_subs_given                       false
% 27.35/3.99  --inst_orphan_elimination               true
% 27.35/3.99  --inst_learning_loop_flag               true
% 27.35/3.99  --inst_learning_start                   3000
% 27.35/3.99  --inst_learning_factor                  2
% 27.35/3.99  --inst_start_prop_sim_after_learn       3
% 27.35/3.99  --inst_sel_renew                        solver
% 27.35/3.99  --inst_lit_activity_flag                true
% 27.35/3.99  --inst_restr_to_given                   false
% 27.35/3.99  --inst_activity_threshold               500
% 27.35/3.99  --inst_out_proof                        true
% 27.35/3.99  
% 27.35/3.99  ------ Resolution Options
% 27.35/3.99  
% 27.35/3.99  --resolution_flag                       true
% 27.35/3.99  --res_lit_sel                           adaptive
% 27.35/3.99  --res_lit_sel_side                      none
% 27.35/3.99  --res_ordering                          kbo
% 27.35/3.99  --res_to_prop_solver                    active
% 27.35/3.99  --res_prop_simpl_new                    false
% 27.35/3.99  --res_prop_simpl_given                  true
% 27.35/3.99  --res_passive_queue_type                priority_queues
% 27.35/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.35/3.99  --res_passive_queues_freq               [15;5]
% 27.35/3.99  --res_forward_subs                      full
% 27.35/3.99  --res_backward_subs                     full
% 27.35/3.99  --res_forward_subs_resolution           true
% 27.35/3.99  --res_backward_subs_resolution          true
% 27.35/3.99  --res_orphan_elimination                true
% 27.35/3.99  --res_time_limit                        2.
% 27.35/3.99  --res_out_proof                         true
% 27.35/3.99  
% 27.35/3.99  ------ Superposition Options
% 27.35/3.99  
% 27.35/3.99  --superposition_flag                    true
% 27.35/3.99  --sup_passive_queue_type                priority_queues
% 27.35/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.35/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.35/3.99  --demod_completeness_check              fast
% 27.35/3.99  --demod_use_ground                      true
% 27.35/3.99  --sup_to_prop_solver                    passive
% 27.35/3.99  --sup_prop_simpl_new                    true
% 27.35/3.99  --sup_prop_simpl_given                  true
% 27.35/3.99  --sup_fun_splitting                     true
% 27.35/3.99  --sup_smt_interval                      50000
% 27.35/3.99  
% 27.35/3.99  ------ Superposition Simplification Setup
% 27.35/3.99  
% 27.35/3.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.35/3.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.35/3.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.35/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.35/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.35/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.35/3.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.35/3.99  --sup_immed_triv                        [TrivRules]
% 27.35/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/3.99  --sup_immed_bw_main                     []
% 27.35/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.35/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.35/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/3.99  --sup_input_bw                          []
% 27.35/3.99  
% 27.35/3.99  ------ Combination Options
% 27.35/3.99  
% 27.35/3.99  --comb_res_mult                         3
% 27.35/3.99  --comb_sup_mult                         2
% 27.35/3.99  --comb_inst_mult                        10
% 27.35/3.99  
% 27.35/3.99  ------ Debug Options
% 27.35/3.99  
% 27.35/3.99  --dbg_backtrace                         false
% 27.35/3.99  --dbg_dump_prop_clauses                 false
% 27.35/3.99  --dbg_dump_prop_clauses_file            -
% 27.35/3.99  --dbg_out_stat                          false
% 27.35/3.99  ------ Parsing...
% 27.35/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.35/3.99  
% 27.35/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.35/3.99  
% 27.35/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.35/3.99  
% 27.35/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.35/3.99  ------ Proving...
% 27.35/3.99  ------ Problem Properties 
% 27.35/3.99  
% 27.35/3.99  
% 27.35/3.99  clauses                                 47
% 27.35/3.99  conjectures                             13
% 27.35/3.99  EPR                                     10
% 27.35/3.99  Horn                                    38
% 27.35/3.99  unary                                   12
% 27.35/3.99  binary                                  12
% 27.35/3.99  lits                                    152
% 27.35/3.99  lits eq                                 2
% 27.35/3.99  fd_pure                                 0
% 27.35/3.99  fd_pseudo                               0
% 27.35/3.99  fd_cond                                 0
% 27.35/3.99  fd_pseudo_cond                          1
% 27.35/3.99  AC symbols                              0
% 27.35/3.99  
% 27.35/3.99  ------ Schedule dynamic 5 is on 
% 27.35/3.99  
% 27.35/3.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.35/3.99  
% 27.35/3.99  
% 27.35/3.99  ------ 
% 27.35/3.99  Current options:
% 27.35/3.99  ------ 
% 27.35/3.99  
% 27.35/3.99  ------ Input Options
% 27.35/3.99  
% 27.35/3.99  --out_options                           all
% 27.35/3.99  --tptp_safe_out                         true
% 27.35/3.99  --problem_path                          ""
% 27.35/3.99  --include_path                          ""
% 27.35/3.99  --clausifier                            res/vclausify_rel
% 27.35/3.99  --clausifier_options                    ""
% 27.35/3.99  --stdin                                 false
% 27.35/3.99  --stats_out                             all
% 27.35/3.99  
% 27.35/3.99  ------ General Options
% 27.35/3.99  
% 27.35/3.99  --fof                                   false
% 27.35/3.99  --time_out_real                         305.
% 27.35/3.99  --time_out_virtual                      -1.
% 27.35/3.99  --symbol_type_check                     false
% 27.35/3.99  --clausify_out                          false
% 27.35/3.99  --sig_cnt_out                           false
% 27.35/3.99  --trig_cnt_out                          false
% 27.35/3.99  --trig_cnt_out_tolerance                1.
% 27.35/3.99  --trig_cnt_out_sk_spl                   false
% 27.35/3.99  --abstr_cl_out                          false
% 27.35/3.99  
% 27.35/3.99  ------ Global Options
% 27.35/3.99  
% 27.35/3.99  --schedule                              default
% 27.35/3.99  --add_important_lit                     false
% 27.35/3.99  --prop_solver_per_cl                    1000
% 27.35/3.99  --min_unsat_core                        false
% 27.35/3.99  --soft_assumptions                      false
% 27.35/3.99  --soft_lemma_size                       3
% 27.35/3.99  --prop_impl_unit_size                   0
% 27.35/3.99  --prop_impl_unit                        []
% 27.35/3.99  --share_sel_clauses                     true
% 27.35/3.99  --reset_solvers                         false
% 27.35/3.99  --bc_imp_inh                            [conj_cone]
% 27.35/3.99  --conj_cone_tolerance                   3.
% 27.35/3.99  --extra_neg_conj                        none
% 27.35/3.99  --large_theory_mode                     true
% 27.35/3.99  --prolific_symb_bound                   200
% 27.35/3.99  --lt_threshold                          2000
% 27.35/3.99  --clause_weak_htbl                      true
% 27.35/3.99  --gc_record_bc_elim                     false
% 27.35/3.99  
% 27.35/3.99  ------ Preprocessing Options
% 27.35/3.99  
% 27.35/3.99  --preprocessing_flag                    true
% 27.35/3.99  --time_out_prep_mult                    0.1
% 27.35/3.99  --splitting_mode                        input
% 27.35/3.99  --splitting_grd                         true
% 27.35/3.99  --splitting_cvd                         false
% 27.35/3.99  --splitting_cvd_svl                     false
% 27.35/3.99  --splitting_nvd                         32
% 27.35/3.99  --sub_typing                            true
% 27.35/3.99  --prep_gs_sim                           true
% 27.35/3.99  --prep_unflatten                        true
% 27.35/3.99  --prep_res_sim                          true
% 27.35/3.99  --prep_upred                            true
% 27.35/3.99  --prep_sem_filter                       exhaustive
% 27.35/3.99  --prep_sem_filter_out                   false
% 27.35/3.99  --pred_elim                             true
% 27.35/3.99  --res_sim_input                         true
% 27.35/3.99  --eq_ax_congr_red                       true
% 27.35/3.99  --pure_diseq_elim                       true
% 27.35/3.99  --brand_transform                       false
% 27.35/3.99  --non_eq_to_eq                          false
% 27.35/3.99  --prep_def_merge                        true
% 27.35/3.99  --prep_def_merge_prop_impl              false
% 27.35/3.99  --prep_def_merge_mbd                    true
% 27.35/3.99  --prep_def_merge_tr_red                 false
% 27.35/3.99  --prep_def_merge_tr_cl                  false
% 27.35/3.99  --smt_preprocessing                     true
% 27.35/3.99  --smt_ac_axioms                         fast
% 27.35/3.99  --preprocessed_out                      false
% 27.35/3.99  --preprocessed_stats                    false
% 27.35/3.99  
% 27.35/3.99  ------ Abstraction refinement Options
% 27.35/3.99  
% 27.35/3.99  --abstr_ref                             []
% 27.35/3.99  --abstr_ref_prep                        false
% 27.35/3.99  --abstr_ref_until_sat                   false
% 27.35/3.99  --abstr_ref_sig_restrict                funpre
% 27.35/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.35/3.99  --abstr_ref_under                       []
% 27.35/3.99  
% 27.35/3.99  ------ SAT Options
% 27.35/3.99  
% 27.35/3.99  --sat_mode                              false
% 27.35/3.99  --sat_fm_restart_options                ""
% 27.35/3.99  --sat_gr_def                            false
% 27.35/3.99  --sat_epr_types                         true
% 27.35/3.99  --sat_non_cyclic_types                  false
% 27.35/3.99  --sat_finite_models                     false
% 27.35/3.99  --sat_fm_lemmas                         false
% 27.35/3.99  --sat_fm_prep                           false
% 27.35/3.99  --sat_fm_uc_incr                        true
% 27.35/3.99  --sat_out_model                         small
% 27.35/3.99  --sat_out_clauses                       false
% 27.35/3.99  
% 27.35/3.99  ------ QBF Options
% 27.35/3.99  
% 27.35/3.99  --qbf_mode                              false
% 27.35/3.99  --qbf_elim_univ                         false
% 27.35/3.99  --qbf_dom_inst                          none
% 27.35/3.99  --qbf_dom_pre_inst                      false
% 27.35/3.99  --qbf_sk_in                             false
% 27.35/3.99  --qbf_pred_elim                         true
% 27.35/3.99  --qbf_split                             512
% 27.35/3.99  
% 27.35/3.99  ------ BMC1 Options
% 27.35/3.99  
% 27.35/3.99  --bmc1_incremental                      false
% 27.35/3.99  --bmc1_axioms                           reachable_all
% 27.35/3.99  --bmc1_min_bound                        0
% 27.35/3.99  --bmc1_max_bound                        -1
% 27.35/3.99  --bmc1_max_bound_default                -1
% 27.35/3.99  --bmc1_symbol_reachability              true
% 27.35/3.99  --bmc1_property_lemmas                  false
% 27.35/3.99  --bmc1_k_induction                      false
% 27.35/3.99  --bmc1_non_equiv_states                 false
% 27.35/3.99  --bmc1_deadlock                         false
% 27.35/3.99  --bmc1_ucm                              false
% 27.35/3.99  --bmc1_add_unsat_core                   none
% 27.35/3.99  --bmc1_unsat_core_children              false
% 27.35/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.35/3.99  --bmc1_out_stat                         full
% 27.35/3.99  --bmc1_ground_init                      false
% 27.35/3.99  --bmc1_pre_inst_next_state              false
% 27.35/3.99  --bmc1_pre_inst_state                   false
% 27.35/3.99  --bmc1_pre_inst_reach_state             false
% 27.35/3.99  --bmc1_out_unsat_core                   false
% 27.35/3.99  --bmc1_aig_witness_out                  false
% 27.35/3.99  --bmc1_verbose                          false
% 27.35/3.99  --bmc1_dump_clauses_tptp                false
% 27.35/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.35/3.99  --bmc1_dump_file                        -
% 27.35/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.35/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.35/3.99  --bmc1_ucm_extend_mode                  1
% 27.35/3.99  --bmc1_ucm_init_mode                    2
% 27.35/3.99  --bmc1_ucm_cone_mode                    none
% 27.35/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.35/3.99  --bmc1_ucm_relax_model                  4
% 27.35/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.35/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.35/3.99  --bmc1_ucm_layered_model                none
% 27.35/3.99  --bmc1_ucm_max_lemma_size               10
% 27.35/3.99  
% 27.35/3.99  ------ AIG Options
% 27.35/3.99  
% 27.35/3.99  --aig_mode                              false
% 27.35/3.99  
% 27.35/3.99  ------ Instantiation Options
% 27.35/3.99  
% 27.35/3.99  --instantiation_flag                    true
% 27.35/3.99  --inst_sos_flag                         true
% 27.35/3.99  --inst_sos_phase                        true
% 27.35/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.35/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.35/3.99  --inst_lit_sel_side                     none
% 27.35/3.99  --inst_solver_per_active                1400
% 27.35/3.99  --inst_solver_calls_frac                1.
% 27.35/3.99  --inst_passive_queue_type               priority_queues
% 27.35/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.35/3.99  --inst_passive_queues_freq              [25;2]
% 27.35/3.99  --inst_dismatching                      true
% 27.35/3.99  --inst_eager_unprocessed_to_passive     true
% 27.35/3.99  --inst_prop_sim_given                   true
% 27.35/3.99  --inst_prop_sim_new                     false
% 27.35/3.99  --inst_subs_new                         false
% 27.35/3.99  --inst_eq_res_simp                      false
% 27.35/3.99  --inst_subs_given                       false
% 27.35/3.99  --inst_orphan_elimination               true
% 27.35/3.99  --inst_learning_loop_flag               true
% 27.35/3.99  --inst_learning_start                   3000
% 27.35/3.99  --inst_learning_factor                  2
% 27.35/3.99  --inst_start_prop_sim_after_learn       3
% 27.35/3.99  --inst_sel_renew                        solver
% 27.35/3.99  --inst_lit_activity_flag                true
% 27.35/3.99  --inst_restr_to_given                   false
% 27.35/3.99  --inst_activity_threshold               500
% 27.35/3.99  --inst_out_proof                        true
% 27.35/3.99  
% 27.35/3.99  ------ Resolution Options
% 27.35/3.99  
% 27.35/3.99  --resolution_flag                       false
% 27.35/3.99  --res_lit_sel                           adaptive
% 27.35/3.99  --res_lit_sel_side                      none
% 27.35/3.99  --res_ordering                          kbo
% 27.35/3.99  --res_to_prop_solver                    active
% 27.35/3.99  --res_prop_simpl_new                    false
% 27.35/3.99  --res_prop_simpl_given                  true
% 27.35/3.99  --res_passive_queue_type                priority_queues
% 27.35/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.35/3.99  --res_passive_queues_freq               [15;5]
% 27.35/3.99  --res_forward_subs                      full
% 27.35/3.99  --res_backward_subs                     full
% 27.35/3.99  --res_forward_subs_resolution           true
% 27.35/3.99  --res_backward_subs_resolution          true
% 27.35/3.99  --res_orphan_elimination                true
% 27.35/3.99  --res_time_limit                        2.
% 27.35/3.99  --res_out_proof                         true
% 27.35/3.99  
% 27.35/3.99  ------ Superposition Options
% 27.35/3.99  
% 27.35/3.99  --superposition_flag                    true
% 27.35/3.99  --sup_passive_queue_type                priority_queues
% 27.35/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.35/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.35/3.99  --demod_completeness_check              fast
% 27.35/3.99  --demod_use_ground                      true
% 27.35/3.99  --sup_to_prop_solver                    passive
% 27.35/3.99  --sup_prop_simpl_new                    true
% 27.35/3.99  --sup_prop_simpl_given                  true
% 27.35/3.99  --sup_fun_splitting                     true
% 27.35/3.99  --sup_smt_interval                      50000
% 27.35/3.99  
% 27.35/3.99  ------ Superposition Simplification Setup
% 27.35/3.99  
% 27.35/3.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.35/3.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.35/3.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.35/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.35/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.35/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.35/3.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.35/3.99  --sup_immed_triv                        [TrivRules]
% 27.35/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/3.99  --sup_immed_bw_main                     []
% 27.35/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.35/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.35/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/3.99  --sup_input_bw                          []
% 27.35/3.99  
% 27.35/3.99  ------ Combination Options
% 27.35/3.99  
% 27.35/3.99  --comb_res_mult                         3
% 27.35/3.99  --comb_sup_mult                         2
% 27.35/3.99  --comb_inst_mult                        10
% 27.35/3.99  
% 27.35/3.99  ------ Debug Options
% 27.35/3.99  
% 27.35/3.99  --dbg_backtrace                         false
% 27.35/3.99  --dbg_dump_prop_clauses                 false
% 27.35/3.99  --dbg_dump_prop_clauses_file            -
% 27.35/3.99  --dbg_out_stat                          false
% 27.35/3.99  
% 27.35/3.99  
% 27.35/3.99  
% 27.35/3.99  
% 27.35/3.99  ------ Proving...
% 27.35/3.99  
% 27.35/3.99  
% 27.35/3.99  % SZS status Theorem for theBenchmark.p
% 27.35/3.99  
% 27.35/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.35/3.99  
% 27.35/3.99  fof(f3,axiom,(
% 27.35/3.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 27.35/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.35/3.99  
% 27.35/3.99  fof(f17,plain,(
% 27.35/3.99    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.35/3.99    inference(ennf_transformation,[],[f3])).
% 27.35/3.99  
% 27.35/3.99  fof(f69,plain,(
% 27.35/3.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.35/3.99    inference(cnf_transformation,[],[f17])).
% 27.35/3.99  
% 27.35/3.99  fof(f11,axiom,(
% 27.35/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 27.35/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.35/3.99  
% 27.35/3.99  fof(f29,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.35/3.99    inference(ennf_transformation,[],[f11])).
% 27.35/3.99  
% 27.35/3.99  fof(f30,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.35/3.99    inference(flattening,[],[f29])).
% 27.35/3.99  
% 27.35/3.99  fof(f55,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.35/3.99    inference(nnf_transformation,[],[f30])).
% 27.35/3.99  
% 27.35/3.99  fof(f56,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.35/3.99    inference(flattening,[],[f55])).
% 27.35/3.99  
% 27.35/3.99  fof(f97,plain,(
% 27.35/3.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f56])).
% 27.35/3.99  
% 27.35/3.99  fof(f12,conjecture,(
% 27.35/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 27.35/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.35/3.99  
% 27.35/3.99  fof(f13,negated_conjecture,(
% 27.35/3.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 27.35/3.99    inference(negated_conjecture,[],[f12])).
% 27.35/3.99  
% 27.35/3.99  fof(f31,plain,(
% 27.35/3.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 27.35/3.99    inference(ennf_transformation,[],[f13])).
% 27.35/3.99  
% 27.35/3.99  fof(f32,plain,(
% 27.35/3.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.35/3.99    inference(flattening,[],[f31])).
% 27.35/3.99  
% 27.35/3.99  fof(f57,plain,(
% 27.35/3.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.35/3.99    inference(nnf_transformation,[],[f32])).
% 27.35/3.99  
% 27.35/3.99  fof(f58,plain,(
% 27.35/3.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.35/3.99    inference(flattening,[],[f57])).
% 27.35/3.99  
% 27.35/3.99  fof(f62,plain,(
% 27.35/3.99    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => ((~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & sK8 = X2 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 27.35/3.99    introduced(choice_axiom,[])).
% 27.35/3.99  
% 27.35/3.99  fof(f61,plain,(
% 27.35/3.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(sK7,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(sK7,X0,X1)) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 27.35/3.99    introduced(choice_axiom,[])).
% 27.35/3.99  
% 27.35/3.99  fof(f60,plain,(
% 27.35/3.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK6) | ~v5_pre_topc(X2,X0,sK6)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK6) | v5_pre_topc(X2,X0,sK6)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK6)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK6)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK6)) & v1_funct_1(X2)) & l1_pre_topc(sK6) & v2_pre_topc(sK6))) )),
% 27.35/3.99    introduced(choice_axiom,[])).
% 27.35/3.99  
% 27.35/3.99  fof(f59,plain,(
% 27.35/3.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) | ~v5_pre_topc(X2,sK5,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) | v5_pre_topc(X2,sK5,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5))),
% 27.35/3.99    introduced(choice_axiom,[])).
% 27.35/3.99  
% 27.35/3.99  fof(f63,plain,(
% 27.35/3.99    ((((~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~v5_pre_topc(sK7,sK5,sK6)) & (v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,sK5,sK6)) & sK7 = sK8 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5)),
% 27.35/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f58,f62,f61,f60,f59])).
% 27.35/3.99  
% 27.35/3.99  fof(f105,plain,(
% 27.35/3.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))),
% 27.35/3.99    inference(cnf_transformation,[],[f63])).
% 27.35/3.99  
% 27.35/3.99  fof(f109,plain,(
% 27.35/3.99    sK7 = sK8),
% 27.35/3.99    inference(cnf_transformation,[],[f63])).
% 27.35/3.99  
% 27.35/3.99  fof(f4,axiom,(
% 27.35/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 27.35/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.35/3.99  
% 27.35/3.99  fof(f18,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(ennf_transformation,[],[f4])).
% 27.35/3.99  
% 27.35/3.99  fof(f19,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(flattening,[],[f18])).
% 27.35/3.99  
% 27.35/3.99  fof(f38,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(nnf_transformation,[],[f19])).
% 27.35/3.99  
% 27.35/3.99  fof(f39,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(rectify,[],[f38])).
% 27.35/3.99  
% 27.35/3.99  fof(f40,plain,(
% 27.35/3.99    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0) & v4_pre_topc(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 27.35/3.99    introduced(choice_axiom,[])).
% 27.35/3.99  
% 27.35/3.99  fof(f41,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0) & v4_pre_topc(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 27.35/3.99  
% 27.35/3.99  fof(f70,plain,(
% 27.35/3.99    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f41])).
% 27.35/3.99  
% 27.35/3.99  fof(f99,plain,(
% 27.35/3.99    v2_pre_topc(sK5)),
% 27.35/3.99    inference(cnf_transformation,[],[f63])).
% 27.35/3.99  
% 27.35/3.99  fof(f1,axiom,(
% 27.35/3.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.35/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.35/3.99  
% 27.35/3.99  fof(f35,plain,(
% 27.35/3.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.35/3.99    inference(nnf_transformation,[],[f1])).
% 27.35/3.99  
% 27.35/3.99  fof(f36,plain,(
% 27.35/3.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.35/3.99    inference(flattening,[],[f35])).
% 27.35/3.99  
% 27.35/3.99  fof(f65,plain,(
% 27.35/3.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 27.35/3.99    inference(cnf_transformation,[],[f36])).
% 27.35/3.99  
% 27.35/3.99  fof(f112,plain,(
% 27.35/3.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.35/3.99    inference(equality_resolution,[],[f65])).
% 27.35/3.99  
% 27.35/3.99  fof(f2,axiom,(
% 27.35/3.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.35/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.35/3.99  
% 27.35/3.99  fof(f37,plain,(
% 27.35/3.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.35/3.99    inference(nnf_transformation,[],[f2])).
% 27.35/3.99  
% 27.35/3.99  fof(f68,plain,(
% 27.35/3.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f37])).
% 27.35/3.99  
% 27.35/3.99  fof(f10,axiom,(
% 27.35/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 27.35/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.35/3.99  
% 27.35/3.99  fof(f27,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.35/3.99    inference(ennf_transformation,[],[f10])).
% 27.35/3.99  
% 27.35/3.99  fof(f28,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.35/3.99    inference(flattening,[],[f27])).
% 27.35/3.99  
% 27.35/3.99  fof(f53,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.35/3.99    inference(nnf_transformation,[],[f28])).
% 27.35/3.99  
% 27.35/3.99  fof(f54,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.35/3.99    inference(flattening,[],[f53])).
% 27.35/3.99  
% 27.35/3.99  fof(f92,plain,(
% 27.35/3.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f54])).
% 27.35/3.99  
% 27.35/3.99  fof(f67,plain,(
% 27.35/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.35/3.99    inference(cnf_transformation,[],[f37])).
% 27.35/3.99  
% 27.35/3.99  fof(f5,axiom,(
% 27.35/3.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 27.35/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.35/3.99  
% 27.35/3.99  fof(f14,plain,(
% 27.35/3.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 27.35/3.99    inference(rectify,[],[f5])).
% 27.35/3.99  
% 27.35/3.99  fof(f20,plain,(
% 27.35/3.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(ennf_transformation,[],[f14])).
% 27.35/3.99  
% 27.35/3.99  fof(f21,plain,(
% 27.35/3.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(flattening,[],[f20])).
% 27.35/3.99  
% 27.35/3.99  fof(f33,plain,(
% 27.35/3.99    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 27.35/3.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 27.35/3.99  
% 27.35/3.99  fof(f34,plain,(
% 27.35/3.99    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(definition_folding,[],[f21,f33])).
% 27.35/3.99  
% 27.35/3.99  fof(f47,plain,(
% 27.35/3.99    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(nnf_transformation,[],[f34])).
% 27.35/3.99  
% 27.35/3.99  fof(f48,plain,(
% 27.35/3.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(flattening,[],[f47])).
% 27.35/3.99  
% 27.35/3.99  fof(f49,plain,(
% 27.35/3.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(rectify,[],[f48])).
% 27.35/3.99  
% 27.35/3.99  fof(f50,plain,(
% 27.35/3.99    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0)) & r1_tarski(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 27.35/3.99    introduced(choice_axiom,[])).
% 27.35/3.99  
% 27.35/3.99  fof(f51,plain,(
% 27.35/3.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0)) & r1_tarski(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).
% 27.35/3.99  
% 27.35/3.99  fof(f80,plain,(
% 27.35/3.99    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f51])).
% 27.35/3.99  
% 27.35/3.99  fof(f6,axiom,(
% 27.35/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 27.35/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.35/3.99  
% 27.35/3.99  fof(f22,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(ennf_transformation,[],[f6])).
% 27.35/3.99  
% 27.35/3.99  fof(f52,plain,(
% 27.35/3.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(nnf_transformation,[],[f22])).
% 27.35/3.99  
% 27.35/3.99  fof(f87,plain,(
% 27.35/3.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f52])).
% 27.35/3.99  
% 27.35/3.99  fof(f94,plain,(
% 27.35/3.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f54])).
% 27.35/3.99  
% 27.35/3.99  fof(f9,axiom,(
% 27.35/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 27.35/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.35/3.99  
% 27.35/3.99  fof(f16,plain,(
% 27.35/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 27.35/3.99    inference(pure_predicate_removal,[],[f9])).
% 27.35/3.99  
% 27.35/3.99  fof(f25,plain,(
% 27.35/3.99    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.35/3.99    inference(ennf_transformation,[],[f16])).
% 27.35/3.99  
% 27.35/3.99  fof(f26,plain,(
% 27.35/3.99    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.35/3.99    inference(flattening,[],[f25])).
% 27.35/3.99  
% 27.35/3.99  fof(f90,plain,(
% 27.35/3.99    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f26])).
% 27.35/3.99  
% 27.35/3.99  fof(f8,axiom,(
% 27.35/3.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 27.35/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.35/3.99  
% 27.35/3.99  fof(f24,plain,(
% 27.35/3.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.35/3.99    inference(ennf_transformation,[],[f8])).
% 27.35/3.99  
% 27.35/3.99  fof(f89,plain,(
% 27.35/3.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f24])).
% 27.35/3.99  
% 27.35/3.99  fof(f7,axiom,(
% 27.35/3.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 27.35/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.35/3.99  
% 27.35/3.99  fof(f15,plain,(
% 27.35/3.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 27.35/3.99    inference(pure_predicate_removal,[],[f7])).
% 27.35/3.99  
% 27.35/3.99  fof(f23,plain,(
% 27.35/3.99    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 27.35/3.99    inference(ennf_transformation,[],[f15])).
% 27.35/3.99  
% 27.35/3.99  fof(f88,plain,(
% 27.35/3.99    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 27.35/3.99    inference(cnf_transformation,[],[f23])).
% 27.35/3.99  
% 27.35/3.99  fof(f66,plain,(
% 27.35/3.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f36])).
% 27.35/3.99  
% 27.35/3.99  fof(f100,plain,(
% 27.35/3.99    l1_pre_topc(sK5)),
% 27.35/3.99    inference(cnf_transformation,[],[f63])).
% 27.35/3.99  
% 27.35/3.99  fof(f95,plain,(
% 27.35/3.99    ( ! [X0,X1] : (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f56])).
% 27.35/3.99  
% 27.35/3.99  fof(f73,plain,(
% 27.35/3.99    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f41])).
% 27.35/3.99  
% 27.35/3.99  fof(f72,plain,(
% 27.35/3.99    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v4_pre_topc(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f41])).
% 27.35/3.99  
% 27.35/3.99  fof(f71,plain,(
% 27.35/3.99    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f41])).
% 27.35/3.99  
% 27.35/3.99  fof(f102,plain,(
% 27.35/3.99    l1_pre_topc(sK6)),
% 27.35/3.99    inference(cnf_transformation,[],[f63])).
% 27.35/3.99  
% 27.35/3.99  fof(f106,plain,(
% 27.35/3.99    v1_funct_1(sK8)),
% 27.35/3.99    inference(cnf_transformation,[],[f63])).
% 27.35/3.99  
% 27.35/3.99  fof(f104,plain,(
% 27.35/3.99    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))),
% 27.35/3.99    inference(cnf_transformation,[],[f63])).
% 27.35/3.99  
% 27.35/3.99  fof(f111,plain,(
% 27.35/3.99    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | ~v5_pre_topc(sK7,sK5,sK6)),
% 27.35/3.99    inference(cnf_transformation,[],[f63])).
% 27.35/3.99  
% 27.35/3.99  fof(f93,plain,(
% 27.35/3.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.35/3.99    inference(cnf_transformation,[],[f54])).
% 27.35/3.99  
% 27.35/3.99  fof(f110,plain,(
% 27.35/3.99    v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) | v5_pre_topc(sK7,sK5,sK6)),
% 27.35/3.99    inference(cnf_transformation,[],[f63])).
% 27.35/3.99  
% 27.35/3.99  fof(f64,plain,(
% 27.35/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.35/3.99    inference(cnf_transformation,[],[f36])).
% 27.35/3.99  
% 27.35/3.99  fof(f113,plain,(
% 27.35/3.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.35/3.99    inference(equality_resolution,[],[f64])).
% 27.35/3.99  
% 27.35/3.99  fof(f108,plain,(
% 27.35/3.99    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))),
% 27.35/3.99    inference(cnf_transformation,[],[f63])).
% 27.35/3.99  
% 27.35/3.99  fof(f107,plain,(
% 27.35/3.99    v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))),
% 27.35/3.99    inference(cnf_transformation,[],[f63])).
% 27.35/3.99  
% 27.35/3.99  fof(f103,plain,(
% 27.35/3.99    v1_funct_1(sK7)),
% 27.35/3.99    inference(cnf_transformation,[],[f63])).
% 27.35/3.99  
% 27.35/3.99  cnf(c_3202,plain,
% 27.35/3.99      ( ~ v4_pre_topc(X0,X1) | v4_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.35/3.99      theory(equality) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_53207,plain,
% 27.35/3.99      ( ~ v4_pre_topc(X0,X1)
% 27.35/3.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(sK6),sK7,sK1(X2,sK6,sK7)),X2)
% 27.35/3.99      | X2 != X1
% 27.35/3.99      | k8_relset_1(u1_struct_0(X2),u1_struct_0(sK6),sK7,sK1(X2,sK6,sK7)) != X0 ),
% 27.35/3.99      inference(instantiation,[status(thm)],[c_3202]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_71141,plain,
% 27.35/3.99      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK6),sK7,sK1(X0,sK6,sK7)),X0)
% 27.35/3.99      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
% 27.35/3.99      | X0 != sK5
% 27.35/3.99      | k8_relset_1(u1_struct_0(X0),u1_struct_0(sK6),sK7,sK1(X0,sK6,sK7)) != k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)) ),
% 27.35/3.99      inference(instantiation,[status(thm)],[c_53207]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_71154,plain,
% 27.35/3.99      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
% 27.35/3.99      | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
% 27.35/3.99      | k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)) != k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7))
% 27.35/3.99      | sK5 != sK5 ),
% 27.35/3.99      inference(instantiation,[status(thm)],[c_71141]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_3198,plain,
% 27.35/3.99      ( X0 != X1
% 27.35/3.99      | X2 != X3
% 27.35/3.99      | X4 != X5
% 27.35/3.99      | k8_relset_1(X0,X2,X6,X4) = k8_relset_1(X1,X3,X6,X5) ),
% 27.35/3.99      theory(equality) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_52347,plain,
% 27.35/3.99      ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)) = k8_relset_1(X0,X1,sK7,X2)
% 27.35/3.99      | sK1(sK5,sK6,sK7) != X2
% 27.35/3.99      | u1_struct_0(sK6) != X1
% 27.35/3.99      | u1_struct_0(sK5) != X0 ),
% 27.35/3.99      inference(instantiation,[status(thm)],[c_3198]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_53092,plain,
% 27.35/3.99      ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)) = k8_relset_1(X0,u1_struct_0(sK6),sK7,X1)
% 27.35/3.99      | sK1(sK5,sK6,sK7) != X1
% 27.35/3.99      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 27.35/3.99      | u1_struct_0(sK5) != X0 ),
% 27.35/3.99      inference(instantiation,[status(thm)],[c_52347]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_54526,plain,
% 27.35/3.99      ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(sK6),sK7,X1)
% 27.35/3.99      | sK1(sK5,sK6,sK7) != X1
% 27.35/3.99      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 27.35/3.99      | u1_struct_0(sK5) != u1_struct_0(X0) ),
% 27.35/3.99      inference(instantiation,[status(thm)],[c_53092]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_58315,plain,
% 27.35/3.99      ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7))
% 27.35/3.99      | sK1(sK5,sK6,sK7) != sK1(sK5,sK6,sK7)
% 27.35/3.99      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 27.35/3.99      | u1_struct_0(sK5) != u1_struct_0(X0) ),
% 27.35/3.99      inference(instantiation,[status(thm)],[c_54526]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_67293,plain,
% 27.35/3.99      ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)) = k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7))
% 27.35/3.99      | sK1(sK5,sK6,sK7) != sK1(sK5,sK6,sK7)
% 27.35/3.99      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 27.35/3.99      | u1_struct_0(sK5) != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
% 27.35/3.99      inference(instantiation,[status(thm)],[c_58315]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_5,plain,
% 27.35/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.35/3.99      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 27.35/3.99      inference(cnf_transformation,[],[f69]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_61024,plain,
% 27.35/3.99      ( m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))
% 27.35/3.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) ),
% 27.35/3.99      inference(instantiation,[status(thm)],[c_5]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_32,plain,
% 27.35/3.99      ( v4_pre_topc(X0,X1)
% 27.35/3.99      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 27.35/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 27.35/3.99      | ~ v2_pre_topc(X1)
% 27.35/3.99      | ~ l1_pre_topc(X1) ),
% 27.35/3.99      inference(cnf_transformation,[],[f97]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_5812,plain,
% 27.35/3.99      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 27.35/3.99      | v4_pre_topc(X0,sK5)
% 27.35/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))
% 27.35/3.99      | ~ v2_pre_topc(sK5)
% 27.35/3.99      | ~ l1_pre_topc(sK5) ),
% 27.35/3.99      inference(instantiation,[status(thm)],[c_32]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_7282,plain,
% 27.35/3.99      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0),X1,X2),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 27.35/3.99      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0),X1,X2),sK5)
% 27.35/3.99      | ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))
% 27.35/3.99      | ~ v2_pre_topc(sK5)
% 27.35/3.99      | ~ l1_pre_topc(sK5) ),
% 27.35/3.99      inference(instantiation,[status(thm)],[c_5812]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_10168,plain,
% 27.35/3.99      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0),sK7,X1),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 27.35/3.99      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0),sK7,X1),sK5)
% 27.35/3.99      | ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0),sK7,X1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))
% 27.35/3.99      | ~ v2_pre_topc(sK5)
% 27.35/3.99      | ~ l1_pre_topc(sK5) ),
% 27.35/3.99      inference(instantiation,[status(thm)],[c_7282]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_47314,plain,
% 27.35/3.99      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 27.35/3.99      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
% 27.35/3.99      | ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))
% 27.35/3.99      | ~ v2_pre_topc(sK5)
% 27.35/3.99      | ~ l1_pre_topc(sK5) ),
% 27.35/3.99      inference(instantiation,[status(thm)],[c_10168]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_41,negated_conjecture,
% 27.35/3.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
% 27.35/3.99      inference(cnf_transformation,[],[f105]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4240,plain,
% 27.35/3.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_37,negated_conjecture,
% 27.35/3.99      ( sK7 = sK8 ),
% 27.35/3.99      inference(cnf_transformation,[],[f109]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4282,plain,
% 27.35/3.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
% 27.35/3.99      inference(light_normalisation,[status(thm)],[c_4240,c_37]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_9,plain,
% 27.35/3.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.35/3.99      | ~ v5_pre_topc(X0,X1,X2)
% 27.35/3.99      | ~ v4_pre_topc(X3,X2)
% 27.35/3.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 27.35/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.35/3.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 27.35/3.99      | ~ l1_pre_topc(X2)
% 27.35/3.99      | ~ l1_pre_topc(X1)
% 27.35/3.99      | ~ v1_funct_1(X0) ),
% 27.35/3.99      inference(cnf_transformation,[],[f70]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4271,plain,
% 27.35/3.99      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 27.35/3.99      | v5_pre_topc(X0,X1,X2) != iProver_top
% 27.35/3.99      | v4_pre_topc(X3,X2) != iProver_top
% 27.35/3.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1) = iProver_top
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 27.35/3.99      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 27.35/3.99      | l1_pre_topc(X1) != iProver_top
% 27.35/3.99      | l1_pre_topc(X2) != iProver_top
% 27.35/3.99      | v1_funct_1(X0) != iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4275,plain,
% 27.35/3.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.35/3.99      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_47,negated_conjecture,
% 27.35/3.99      ( v2_pre_topc(sK5) ),
% 27.35/3.99      inference(cnf_transformation,[],[f99]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4234,plain,
% 27.35/3.99      ( v2_pre_topc(sK5) = iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_1,plain,
% 27.35/3.99      ( r1_tarski(X0,X0) ),
% 27.35/3.99      inference(cnf_transformation,[],[f112]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4278,plain,
% 27.35/3.99      ( r1_tarski(X0,X0) = iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_3,plain,
% 27.35/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.35/3.99      inference(cnf_transformation,[],[f68]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4277,plain,
% 27.35/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 27.35/3.99      | r1_tarski(X0,X1) != iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_29,plain,
% 27.35/3.99      ( ~ v3_pre_topc(X0,X1)
% 27.35/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 27.35/3.99      | ~ v2_pre_topc(X1)
% 27.35/3.99      | ~ l1_pre_topc(X1) ),
% 27.35/3.99      inference(cnf_transformation,[],[f92]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4251,plain,
% 27.35/3.99      ( v3_pre_topc(X0,X1) != iProver_top
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
% 27.35/3.99      | v2_pre_topc(X1) != iProver_top
% 27.35/3.99      | l1_pre_topc(X1) != iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4,plain,
% 27.35/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.35/3.99      inference(cnf_transformation,[],[f67]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4276,plain,
% 27.35/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.35/3.99      | r1_tarski(X0,X1) = iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_6624,plain,
% 27.35/3.99      ( v3_pre_topc(X0,X1) != iProver_top
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.35/3.99      | r1_tarski(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) = iProver_top
% 27.35/3.99      | v2_pre_topc(X1) != iProver_top
% 27.35/3.99      | l1_pre_topc(X1) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_4251,c_4276]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_21,plain,
% 27.35/3.99      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 27.35/3.99      | ~ v2_pre_topc(X0)
% 27.35/3.99      | ~ l1_pre_topc(X0) ),
% 27.35/3.99      inference(cnf_transformation,[],[f80]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4259,plain,
% 27.35/3.99      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 27.35/3.99      | v2_pre_topc(X0) != iProver_top
% 27.35/3.99      | l1_pre_topc(X0) != iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_22,plain,
% 27.35/3.99      ( v3_pre_topc(X0,X1)
% 27.35/3.99      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 27.35/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.35/3.99      | ~ l1_pre_topc(X1) ),
% 27.35/3.99      inference(cnf_transformation,[],[f87]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4258,plain,
% 27.35/3.99      ( v3_pre_topc(X0,X1) = iProver_top
% 27.35/3.99      | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.35/3.99      | l1_pre_topc(X1) != iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_6118,plain,
% 27.35/3.99      ( v3_pre_topc(X0,X1) = iProver_top
% 27.35/3.99      | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 27.35/3.99      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 27.35/3.99      | l1_pre_topc(X1) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_4277,c_4258]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_6283,plain,
% 27.35/3.99      ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
% 27.35/3.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top
% 27.35/3.99      | v2_pre_topc(X0) != iProver_top
% 27.35/3.99      | l1_pre_topc(X0) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_4259,c_6118]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_6290,plain,
% 27.35/3.99      ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
% 27.35/3.99      | v2_pre_topc(X0) != iProver_top
% 27.35/3.99      | l1_pre_topc(X0) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_4278,c_6283]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_27,plain,
% 27.35/3.99      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.35/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 27.35/3.99      | ~ v2_pre_topc(X1)
% 27.35/3.99      | ~ l1_pre_topc(X1) ),
% 27.35/3.99      inference(cnf_transformation,[],[f94]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4253,plain,
% 27.35/3.99      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 27.35/3.99      | v2_pre_topc(X1) != iProver_top
% 27.35/3.99      | l1_pre_topc(X1) != iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_6827,plain,
% 27.35/3.99      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 27.35/3.99      | r1_tarski(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 27.35/3.99      | v2_pre_topc(X1) != iProver_top
% 27.35/3.99      | l1_pre_topc(X1) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_4277,c_4253]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_8182,plain,
% 27.35/3.99      ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 27.35/3.99      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 27.35/3.99      | v2_pre_topc(X0) != iProver_top
% 27.35/3.99      | l1_pre_topc(X0) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_4278,c_6827]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_8272,plain,
% 27.35/3.99      ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 27.35/3.99      | v2_pre_topc(X0) != iProver_top
% 27.35/3.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 27.35/3.99      | l1_pre_topc(X0) != iProver_top
% 27.35/3.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_6290,c_8182]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_26,plain,
% 27.35/3.99      ( ~ v2_pre_topc(X0)
% 27.35/3.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 27.35/3.99      | ~ l1_pre_topc(X0) ),
% 27.35/3.99      inference(cnf_transformation,[],[f90]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_84,plain,
% 27.35/3.99      ( v2_pre_topc(X0) != iProver_top
% 27.35/3.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 27.35/3.99      | l1_pre_topc(X0) != iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_25,plain,
% 27.35/3.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 27.35/3.99      | ~ l1_pre_topc(X0) ),
% 27.35/3.99      inference(cnf_transformation,[],[f89]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4255,plain,
% 27.35/3.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 27.35/3.99      | l1_pre_topc(X0) != iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_24,plain,
% 27.35/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 27.35/3.99      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 27.35/3.99      inference(cnf_transformation,[],[f88]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4256,plain,
% 27.35/3.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 27.35/3.99      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_5028,plain,
% 27.35/3.99      ( l1_pre_topc(X0) != iProver_top
% 27.35/3.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_4255,c_4256]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_8494,plain,
% 27.35/3.99      ( l1_pre_topc(X0) != iProver_top
% 27.35/3.99      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 27.35/3.99      | v2_pre_topc(X0) != iProver_top ),
% 27.35/3.99      inference(global_propositional_subsumption,
% 27.35/3.99                [status(thm)],
% 27.35/3.99                [c_8272,c_84,c_5028]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_8495,plain,
% 27.35/3.99      ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 27.35/3.99      | v2_pre_topc(X0) != iProver_top
% 27.35/3.99      | l1_pre_topc(X0) != iProver_top ),
% 27.35/3.99      inference(renaming,[status(thm)],[c_8494]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_8500,plain,
% 27.35/3.99      ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X0)) = iProver_top
% 27.35/3.99      | v2_pre_topc(X0) != iProver_top
% 27.35/3.99      | l1_pre_topc(X0) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_8495,c_4276]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_0,plain,
% 27.35/3.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 27.35/3.99      inference(cnf_transformation,[],[f66]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4279,plain,
% 27.35/3.99      ( X0 = X1
% 27.35/3.99      | r1_tarski(X0,X1) != iProver_top
% 27.35/3.99      | r1_tarski(X1,X0) != iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_8613,plain,
% 27.35/3.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0)
% 27.35/3.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 27.35/3.99      | v2_pre_topc(X0) != iProver_top
% 27.35/3.99      | l1_pre_topc(X0) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_8500,c_4279]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_8623,plain,
% 27.35/3.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0)
% 27.35/3.99      | v3_pre_topc(u1_struct_0(X0),X0) != iProver_top
% 27.35/3.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 27.35/3.99      | v2_pre_topc(X0) != iProver_top
% 27.35/3.99      | l1_pre_topc(X0) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_6624,c_8613]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_8707,plain,
% 27.35/3.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0)
% 27.35/3.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 27.35/3.99      | v2_pre_topc(X0) != iProver_top
% 27.35/3.99      | l1_pre_topc(X0) != iProver_top ),
% 27.35/3.99      inference(global_propositional_subsumption,
% 27.35/3.99                [status(thm)],
% 27.35/3.99                [c_8623,c_6290]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_8713,plain,
% 27.35/3.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0)
% 27.35/3.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top
% 27.35/3.99      | v2_pre_topc(X0) != iProver_top
% 27.35/3.99      | l1_pre_topc(X0) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_4277,c_8707]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_8797,plain,
% 27.35/3.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0)
% 27.35/3.99      | v2_pre_topc(X0) != iProver_top
% 27.35/3.99      | l1_pre_topc(X0) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_4278,c_8713]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_8855,plain,
% 27.35/3.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
% 27.35/3.99      | l1_pre_topc(sK5) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_4234,c_8797]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_48,plain,
% 27.35/3.99      ( v2_pre_topc(sK5) = iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_46,negated_conjecture,
% 27.35/3.99      ( l1_pre_topc(sK5) ),
% 27.35/3.99      inference(cnf_transformation,[],[f100]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_49,plain,
% 27.35/3.99      ( l1_pre_topc(sK5) = iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_8801,plain,
% 27.35/3.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
% 27.35/3.99      | v2_pre_topc(sK5) != iProver_top
% 27.35/3.99      | l1_pre_topc(sK5) != iProver_top ),
% 27.35/3.99      inference(instantiation,[status(thm)],[c_8797]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_9186,plain,
% 27.35/3.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5) ),
% 27.35/3.99      inference(global_propositional_subsumption,
% 27.35/3.99                [status(thm)],
% 27.35/3.99                [c_8855,c_48,c_49,c_8801]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_34,plain,
% 27.35/3.99      ( ~ v4_pre_topc(X0,X1)
% 27.35/3.99      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 27.35/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.35/3.99      | ~ v2_pre_topc(X1)
% 27.35/3.99      | ~ l1_pre_topc(X1) ),
% 27.35/3.99      inference(cnf_transformation,[],[f95]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4246,plain,
% 27.35/3.99      ( v4_pre_topc(X0,X1) != iProver_top
% 27.35/3.99      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.35/3.99      | v2_pre_topc(X1) != iProver_top
% 27.35/3.99      | l1_pre_topc(X1) != iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_6,plain,
% 27.35/3.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.35/3.99      | v5_pre_topc(X0,X1,X2)
% 27.35/3.99      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X1)
% 27.35/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.35/3.99      | ~ l1_pre_topc(X2)
% 27.35/3.99      | ~ l1_pre_topc(X1)
% 27.35/3.99      | ~ v1_funct_1(X0) ),
% 27.35/3.99      inference(cnf_transformation,[],[f73]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_4274,plain,
% 27.35/3.99      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 27.35/3.99      | v5_pre_topc(X0,X1,X2) = iProver_top
% 27.35/3.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X1) != iProver_top
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 27.35/3.99      | l1_pre_topc(X1) != iProver_top
% 27.35/3.99      | l1_pre_topc(X2) != iProver_top
% 27.35/3.99      | v1_funct_1(X0) != iProver_top ),
% 27.35/3.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_7269,plain,
% 27.35/3.99      ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 27.35/3.99      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 27.35/3.99      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2),X0,sK1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2,X0)),X1) != iProver_top
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 27.35/3.99      | m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2),X0,sK1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2,X0)),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.35/3.99      | v2_pre_topc(X1) != iProver_top
% 27.35/3.99      | l1_pre_topc(X2) != iProver_top
% 27.35/3.99      | l1_pre_topc(X1) != iProver_top
% 27.35/3.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 27.35/3.99      | v1_funct_1(X0) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_4246,c_4274]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_20000,plain,
% 27.35/3.99      ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1)) != iProver_top
% 27.35/3.99      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/3.99      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),sK5) != iProver_top
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1)))) != iProver_top
% 27.35/3.99      | m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.35/3.99      | v2_pre_topc(sK5) != iProver_top
% 27.35/3.99      | l1_pre_topc(X1) != iProver_top
% 27.35/3.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/3.99      | l1_pre_topc(sK5) != iProver_top
% 27.35/3.99      | v1_funct_1(X0) != iProver_top ),
% 27.35/3.99      inference(superposition,[status(thm)],[c_9186,c_7269]) ).
% 27.35/3.99  
% 27.35/3.99  cnf(c_20039,plain,
% 27.35/3.99      ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
% 27.35/3.99      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/3.99      | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),sK5) != iProver_top
% 27.35/3.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/3.99      | m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.35/4.00      | v2_pre_topc(sK5) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | l1_pre_topc(sK5) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_20000,c_9186]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_9229,plain,
% 27.35/4.00      ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_9186,c_4274]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_9293,plain,
% 27.35/4.00      ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_9229,c_9186]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_87,plain,
% 27.35/4.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 27.35/4.00      | l1_pre_topc(X0) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_89,plain,
% 27.35/4.00      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
% 27.35/4.00      | l1_pre_topc(sK5) != iProver_top ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_87]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4378,plain,
% 27.35/4.00      ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 27.35/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_24]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4379,plain,
% 27.35/4.00      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
% 27.35/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_4378]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_19879,plain,
% 27.35/4.00      ( l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_9293,c_49,c_89,c_4379]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_19880,plain,
% 27.35/4.00      ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(renaming,[status(thm)],[c_19879]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_19885,plain,
% 27.35/4.00      ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),sK5) != iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.35/4.00      | v2_pre_topc(sK5) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | l1_pre_topc(sK5) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_4246,c_19880]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_24710,plain,
% 27.35/4.00      ( m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),sK5) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_20039,c_48,c_49,c_19885]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_24711,plain,
% 27.35/4.00      ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),sK5) != iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(renaming,[status(thm)],[c_24710]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_24717,plain,
% 27.35/4.00      ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X0,sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0)),sK5) != iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_4275,c_24711]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_26513,plain,
% 27.35/4.00      ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | v5_pre_topc(X0,sK5,X1) != iProver_top
% 27.35/4.00      | v4_pre_topc(sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0),X1) != iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | l1_pre_topc(sK5) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_4271,c_24717]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_7,plain,
% 27.35/4.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.35/4.00      | v5_pre_topc(X0,X1,X2)
% 27.35/4.00      | v4_pre_topc(sK1(X1,X2,X0),X2)
% 27.35/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.35/4.00      | ~ l1_pre_topc(X2)
% 27.35/4.00      | ~ l1_pre_topc(X1)
% 27.35/4.00      | ~ v1_funct_1(X0) ),
% 27.35/4.00      inference(cnf_transformation,[],[f72]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4273,plain,
% 27.35/4.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,X1,X2) = iProver_top
% 27.35/4.00      | v4_pre_topc(sK1(X1,X2,X0),X2) = iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | l1_pre_topc(X2) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_9231,plain,
% 27.35/4.00      ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | v4_pre_topc(sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0),X1) = iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_9186,c_4273]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_9291,plain,
% 27.35/4.00      ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | v4_pre_topc(sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0),X1) = iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_9231,c_9186]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_8,plain,
% 27.35/4.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.35/4.00      | v5_pre_topc(X0,X1,X2)
% 27.35/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.35/4.00      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 27.35/4.00      | ~ l1_pre_topc(X2)
% 27.35/4.00      | ~ l1_pre_topc(X1)
% 27.35/4.00      | ~ v1_funct_1(X0) ),
% 27.35/4.00      inference(cnf_transformation,[],[f71]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4272,plain,
% 27.35/4.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,X1,X2) = iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 27.35/4.00      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | l1_pre_topc(X2) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_9230,plain,
% 27.35/4.00      ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_9186,c_4272]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_9292,plain,
% 27.35/4.00      ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_9230,c_9186]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_42493,plain,
% 27.35/4.00      ( l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,sK5,X1) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_26513,c_49,c_89,c_4379,c_9291,c_9292]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_42494,plain,
% 27.35/4.00      ( v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) != iProver_top
% 27.35/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1) = iProver_top
% 27.35/4.00      | v5_pre_topc(X0,sK5,X1) != iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top
% 27.35/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.35/4.00      inference(renaming,[status(thm)],[c_42493]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_42501,plain,
% 27.35/4.00      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
% 27.35/4.00      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
% 27.35/4.00      | v5_pre_topc(sK8,sK5,sK6) != iProver_top
% 27.35/4.00      | l1_pre_topc(sK6) != iProver_top
% 27.35/4.00      | v1_funct_1(sK8) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_4282,c_42494]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_44,negated_conjecture,
% 27.35/4.00      ( l1_pre_topc(sK6) ),
% 27.35/4.00      inference(cnf_transformation,[],[f102]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_51,plain,
% 27.35/4.00      ( l1_pre_topc(sK6) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_40,negated_conjecture,
% 27.35/4.00      ( v1_funct_1(sK8) ),
% 27.35/4.00      inference(cnf_transformation,[],[f106]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_55,plain,
% 27.35/4.00      ( v1_funct_1(sK8) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_42,negated_conjecture,
% 27.35/4.00      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
% 27.35/4.00      inference(cnf_transformation,[],[f104]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4239,plain,
% 27.35/4.00      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4281,plain,
% 27.35/4.00      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_4239,c_37]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_35,negated_conjecture,
% 27.35/4.00      ( ~ v5_pre_topc(sK7,sK5,sK6)
% 27.35/4.00      | ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) ),
% 27.35/4.00      inference(cnf_transformation,[],[f111]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4245,plain,
% 27.35/4.00      ( v5_pre_topc(sK7,sK5,sK6) != iProver_top
% 27.35/4.00      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4284,plain,
% 27.35/4.00      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top
% 27.35/4.00      | v5_pre_topc(sK8,sK5,sK6) != iProver_top ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_4245,c_37]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_42629,plain,
% 27.35/4.00      ( v5_pre_topc(sK8,sK5,sK6) != iProver_top ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_42501,c_51,c_55,c_4281,c_4284]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_42631,plain,
% 27.35/4.00      ( ~ v5_pre_topc(sK8,sK5,sK6) ),
% 27.35/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_42629]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3203,plain,
% 27.35/4.00      ( ~ v1_funct_2(X0,X1,X2)
% 27.35/4.00      | v1_funct_2(X3,X4,X5)
% 27.35/4.00      | X3 != X0
% 27.35/4.00      | X4 != X1
% 27.35/4.00      | X5 != X2 ),
% 27.35/4.00      theory(equality) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_11605,plain,
% 27.35/4.00      ( ~ v1_funct_2(X0,X1,X2)
% 27.35/4.00      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 27.35/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != X1
% 27.35/4.00      | u1_struct_0(sK6) != X2
% 27.35/4.00      | sK7 != X0 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_3203]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_17578,plain,
% 27.35/4.00      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 27.35/4.00      | ~ v1_funct_2(sK8,X0,X1)
% 27.35/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != X0
% 27.35/4.00      | u1_struct_0(sK6) != X1
% 27.35/4.00      | sK7 != sK8 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_11605]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_22780,plain,
% 27.35/4.00      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 27.35/4.00      | ~ v1_funct_2(sK8,X0,u1_struct_0(sK6))
% 27.35/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != X0
% 27.35/4.00      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 27.35/4.00      | sK7 != sK8 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_17578]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_36740,plain,
% 27.35/4.00      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 27.35/4.00      | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 27.35/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 27.35/4.00      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 27.35/4.00      | sK7 != sK8 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_22780]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_11546,plain,
% 27.35/4.00      ( ~ v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1))
% 27.35/4.00      | ~ v5_pre_topc(sK7,X0,X1)
% 27.35/4.00      | ~ v4_pre_topc(X2,X1)
% 27.35/4.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,X2),X0)
% 27.35/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.35/4.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 27.35/4.00      | ~ l1_pre_topc(X1)
% 27.35/4.00      | ~ l1_pre_topc(X0)
% 27.35/4.00      | ~ v1_funct_1(sK7) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_9]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_16445,plain,
% 27.35/4.00      ( ~ v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(sK6))
% 27.35/4.00      | ~ v5_pre_topc(sK7,X0,sK6)
% 27.35/4.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),X0)
% 27.35/4.00      | ~ v4_pre_topc(sK1(sK5,sK6,sK7),sK6)
% 27.35/4.00      | ~ m1_subset_1(sK1(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
% 27.35/4.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6))))
% 27.35/4.00      | ~ l1_pre_topc(X0)
% 27.35/4.00      | ~ l1_pre_topc(sK6)
% 27.35/4.00      | ~ v1_funct_1(sK7) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_11546]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_36193,plain,
% 27.35/4.00      ( ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 27.35/4.00      | ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
% 27.35/4.00      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 27.35/4.00      | ~ v4_pre_topc(sK1(sK5,sK6,sK7),sK6)
% 27.35/4.00      | ~ m1_subset_1(sK1(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
% 27.35/4.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
% 27.35/4.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 27.35/4.00      | ~ l1_pre_topc(sK6)
% 27.35/4.00      | ~ v1_funct_1(sK7) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_16445]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3200,plain,
% 27.35/4.00      ( ~ v5_pre_topc(X0,X1,X2)
% 27.35/4.00      | v5_pre_topc(X3,X4,X5)
% 27.35/4.00      | X3 != X0
% 27.35/4.00      | X4 != X1
% 27.35/4.00      | X5 != X2 ),
% 27.35/4.00      theory(equality) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_6867,plain,
% 27.35/4.00      ( ~ v5_pre_topc(X0,X1,X2)
% 27.35/4.00      | v5_pre_topc(sK7,X3,sK6)
% 27.35/4.00      | X3 != X1
% 27.35/4.00      | sK7 != X0
% 27.35/4.00      | sK6 != X2 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_3200]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_10560,plain,
% 27.35/4.00      ( ~ v5_pre_topc(X0,X1,X2)
% 27.35/4.00      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
% 27.35/4.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != X1
% 27.35/4.00      | sK7 != X0
% 27.35/4.00      | sK6 != X2 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_6867]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_12627,plain,
% 27.35/4.00      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
% 27.35/4.00      | ~ v5_pre_topc(sK8,X0,X1)
% 27.35/4.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != X0
% 27.35/4.00      | sK7 != sK8
% 27.35/4.00      | sK6 != X1 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_10560]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_16164,plain,
% 27.35/4.00      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
% 27.35/4.00      | ~ v5_pre_topc(sK8,X0,sK6)
% 27.35/4.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != X0
% 27.35/4.00      | sK7 != sK8
% 27.35/4.00      | sK6 != sK6 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_12627]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_23026,plain,
% 27.35/4.00      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
% 27.35/4.00      | ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
% 27.35/4.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
% 27.35/4.00      | sK7 != sK8
% 27.35/4.00      | sK6 != sK6 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_16164]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3194,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_6216,plain,
% 27.35/4.00      ( X0 != X1 | u1_struct_0(sK5) != X1 | u1_struct_0(sK5) = X0 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_3194]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_8531,plain,
% 27.35/4.00      ( X0 != u1_struct_0(sK5)
% 27.35/4.00      | u1_struct_0(sK5) = X0
% 27.35/4.00      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_6216]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_11956,plain,
% 27.35/4.00      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 27.35/4.00      | u1_struct_0(sK5) = u1_struct_0(X0)
% 27.35/4.00      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_8531]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_20213,plain,
% 27.35/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != u1_struct_0(sK5)
% 27.35/4.00      | u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 27.35/4.00      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_11956]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4590,plain,
% 27.35/4.00      ( ~ v5_pre_topc(X0,X1,X2)
% 27.35/4.00      | v5_pre_topc(sK8,X3,sK6)
% 27.35/4.00      | X3 != X1
% 27.35/4.00      | sK6 != X2
% 27.35/4.00      | sK8 != X0 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_3200]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_6932,plain,
% 27.35/4.00      ( ~ v5_pre_topc(X0,X1,sK6)
% 27.35/4.00      | v5_pre_topc(sK8,X2,sK6)
% 27.35/4.00      | X2 != X1
% 27.35/4.00      | sK6 != sK6
% 27.35/4.00      | sK8 != X0 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_4590]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_18153,plain,
% 27.35/4.00      ( ~ v5_pre_topc(sK7,X0,sK6)
% 27.35/4.00      | v5_pre_topc(sK8,X1,sK6)
% 27.35/4.00      | X1 != X0
% 27.35/4.00      | sK6 != sK6
% 27.35/4.00      | sK8 != sK7 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_6932]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_18155,plain,
% 27.35/4.00      ( ~ v5_pre_topc(sK7,sK5,sK6)
% 27.35/4.00      | v5_pre_topc(sK8,sK5,sK6)
% 27.35/4.00      | sK6 != sK6
% 27.35/4.00      | sK5 != sK5
% 27.35/4.00      | sK8 != sK7 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_18153]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_6902,plain,
% 27.35/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = X1
% 27.35/4.00      | v3_pre_topc(X1,X0) != iProver_top
% 27.35/4.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 27.35/4.00      | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),X1) != iProver_top
% 27.35/4.00      | v2_pre_topc(X0) != iProver_top
% 27.35/4.00      | l1_pre_topc(X0) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_6624,c_4279]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_13350,plain,
% 27.35/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 27.35/4.00      | v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),X0) != iProver_top
% 27.35/4.00      | v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),X1) != iProver_top
% 27.35/4.00      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 27.35/4.00      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.35/4.00      | v2_pre_topc(X0) != iProver_top
% 27.35/4.00      | v2_pre_topc(X1) != iProver_top
% 27.35/4.00      | l1_pre_topc(X0) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_6624,c_6902]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_13362,plain,
% 27.35/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 27.35/4.00      | v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK5) != iProver_top
% 27.35/4.00      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.35/4.00      | v2_pre_topc(sK5) != iProver_top
% 27.35/4.00      | l1_pre_topc(sK5) != iProver_top ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_13350]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3193,plain,( X0 = X0 ),theory(equality) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_11652,plain,
% 27.35/4.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_3193]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3197,plain,
% 27.35/4.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.35/4.00      theory(equality) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_6748,plain,
% 27.35/4.00      ( m1_subset_1(X0,X1)
% 27.35/4.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
% 27.35/4.00      | X1 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))
% 27.35/4.00      | X0 != sK8 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_3197]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_7428,plain,
% 27.35/4.00      ( m1_subset_1(sK7,X0)
% 27.35/4.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
% 27.35/4.00      | X0 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))
% 27.35/4.00      | sK7 != sK8 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_6748]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_10710,plain,
% 27.35/4.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
% 27.35/4.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
% 27.35/4.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))
% 27.35/4.00      | sK7 != sK8 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_7428]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_8314,plain,
% 27.35/4.00      ( r1_tarski(sK1(sK5,sK6,sK7),sK1(sK5,sK6,sK7)) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_1]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_8274,plain,
% 27.35/4.00      ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 27.35/4.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | v2_pre_topc(sK5) != iProver_top
% 27.35/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | l1_pre_topc(sK5) != iProver_top ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_8272]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_5887,plain,
% 27.35/4.00      ( ~ r1_tarski(X0,sK1(sK5,sK6,sK7))
% 27.35/4.00      | ~ r1_tarski(sK1(sK5,sK6,sK7),X0)
% 27.35/4.00      | sK1(sK5,sK6,sK7) = X0 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_7323,plain,
% 27.35/4.00      ( ~ r1_tarski(sK1(sK5,sK6,sK7),sK1(sK5,sK6,sK7))
% 27.35/4.00      | sK1(sK5,sK6,sK7) = sK1(sK5,sK6,sK7) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_5887]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_28,plain,
% 27.35/4.00      ( v3_pre_topc(X0,X1)
% 27.35/4.00      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 27.35/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 27.35/4.00      | ~ v2_pre_topc(X1)
% 27.35/4.00      | ~ l1_pre_topc(X1) ),
% 27.35/4.00      inference(cnf_transformation,[],[f93]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4252,plain,
% 27.35/4.00      ( v3_pre_topc(X0,X1) = iProver_top
% 27.35/4.00      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 27.35/4.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 27.35/4.00      | v2_pre_topc(X1) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_6811,plain,
% 27.35/4.00      ( v3_pre_topc(X0,X1) = iProver_top
% 27.35/4.00      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 27.35/4.00      | r1_tarski(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 27.35/4.00      | v2_pre_topc(X1) != iProver_top
% 27.35/4.00      | l1_pre_topc(X1) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_4277,c_4252]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_7095,plain,
% 27.35/4.00      ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),X0) = iProver_top
% 27.35/4.00      | v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 27.35/4.00      | v2_pre_topc(X0) != iProver_top
% 27.35/4.00      | l1_pre_topc(X0) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_4278,c_6811]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_7104,plain,
% 27.35/4.00      ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),X0) = iProver_top
% 27.35/4.00      | v2_pre_topc(X0) != iProver_top
% 27.35/4.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 27.35/4.00      | l1_pre_topc(X0) != iProver_top
% 27.35/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_6290,c_7095]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_7106,plain,
% 27.35/4.00      ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),sK5) = iProver_top
% 27.35/4.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | v2_pre_topc(sK5) != iProver_top
% 27.35/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 27.35/4.00      | l1_pre_topc(sK5) != iProver_top ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_7104]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_5963,plain,
% 27.35/4.00      ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_1]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_5181,plain,
% 27.35/4.00      ( ~ r1_tarski(X0,u1_struct_0(sK6))
% 27.35/4.00      | ~ r1_tarski(u1_struct_0(sK6),X0)
% 27.35/4.00      | u1_struct_0(sK6) = X0 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_5606,plain,
% 27.35/4.00      ( ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6))
% 27.35/4.00      | u1_struct_0(sK6) = u1_struct_0(sK6) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_5181]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4604,plain,
% 27.35/4.00      ( X0 != X1 | X0 = sK7 | sK7 != X1 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_3194]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_5097,plain,
% 27.35/4.00      ( X0 = sK7 | X0 != sK8 | sK7 != sK8 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_4604]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_5300,plain,
% 27.35/4.00      ( sK7 != sK8 | sK8 = sK7 | sK8 != sK8 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_5097]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_5055,plain,
% 27.35/4.00      ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_3193]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4955,plain,
% 27.35/4.00      ( r1_tarski(sK8,sK8) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_1]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4564,plain,
% 27.35/4.00      ( ~ r1_tarski(X0,sK8) | ~ r1_tarski(sK8,X0) | X0 = sK8 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4846,plain,
% 27.35/4.00      ( ~ r1_tarski(sK8,sK8) | sK8 = sK8 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_4564]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4526,plain,
% 27.35/4.00      ( r1_tarski(sK6,sK6) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_1]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4385,plain,
% 27.35/4.00      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4452,plain,
% 27.35/4.00      ( ~ r1_tarski(sK6,sK6) | sK6 = sK6 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_4385]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4342,plain,
% 27.35/4.00      ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
% 27.35/4.00      | v5_pre_topc(sK7,sK5,sK6)
% 27.35/4.00      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
% 27.35/4.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
% 27.35/4.00      | ~ l1_pre_topc(sK6)
% 27.35/4.00      | ~ l1_pre_topc(sK5)
% 27.35/4.00      | ~ v1_funct_1(sK7) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_6]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4343,plain,
% 27.35/4.00      ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
% 27.35/4.00      | v5_pre_topc(sK7,sK5,sK6)
% 27.35/4.00      | m1_subset_1(sK1(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
% 27.35/4.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
% 27.35/4.00      | ~ l1_pre_topc(sK6)
% 27.35/4.00      | ~ l1_pre_topc(sK5)
% 27.35/4.00      | ~ v1_funct_1(sK7) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_8]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4344,plain,
% 27.35/4.00      ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
% 27.35/4.00      | v5_pre_topc(sK7,sK5,sK6)
% 27.35/4.00      | v4_pre_topc(sK1(sK5,sK6,sK7),sK6)
% 27.35/4.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
% 27.35/4.00      | ~ l1_pre_topc(sK6)
% 27.35/4.00      | ~ l1_pre_topc(sK5)
% 27.35/4.00      | ~ v1_funct_1(sK7) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_7]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_36,negated_conjecture,
% 27.35/4.00      ( v5_pre_topc(sK7,sK5,sK6)
% 27.35/4.00      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) ),
% 27.35/4.00      inference(cnf_transformation,[],[f110]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4244,plain,
% 27.35/4.00      ( v5_pre_topc(sK7,sK5,sK6) = iProver_top
% 27.35/4.00      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4283,plain,
% 27.35/4.00      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
% 27.35/4.00      | v5_pre_topc(sK8,sK5,sK6) = iProver_top ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_4244,c_37]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4312,plain,
% 27.35/4.00      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
% 27.35/4.00      | v5_pre_topc(sK8,sK5,sK6) ),
% 27.35/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_4283]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3201,plain,
% 27.35/4.00      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 27.35/4.00      theory(equality) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3219,plain,
% 27.35/4.00      ( u1_struct_0(sK5) = u1_struct_0(sK5) | sK5 != sK5 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_3201]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_155,plain,
% 27.35/4.00      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2,plain,
% 27.35/4.00      ( r1_tarski(X0,X0) ),
% 27.35/4.00      inference(cnf_transformation,[],[f113]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_151,plain,
% 27.35/4.00      ( r1_tarski(sK5,sK5) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_2]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_88,plain,
% 27.35/4.00      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 27.35/4.00      | ~ l1_pre_topc(sK5) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_25]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_86,plain,
% 27.35/4.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 27.35/4.00      | v2_pre_topc(sK5) != iProver_top
% 27.35/4.00      | l1_pre_topc(sK5) != iProver_top ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_84]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_38,negated_conjecture,
% 27.35/4.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) ),
% 27.35/4.00      inference(cnf_transformation,[],[f108]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_39,negated_conjecture,
% 27.35/4.00      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) ),
% 27.35/4.00      inference(cnf_transformation,[],[f107]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_43,negated_conjecture,
% 27.35/4.00      ( v1_funct_1(sK7) ),
% 27.35/4.00      inference(cnf_transformation,[],[f103]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(contradiction,plain,
% 27.35/4.00      ( $false ),
% 27.35/4.00      inference(minisat,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_71154,c_67293,c_61024,c_47314,c_42631,c_36740,c_36193,
% 27.35/4.00                 c_23026,c_20213,c_18155,c_13362,c_11652,c_10710,c_8801,
% 27.35/4.00                 c_8314,c_8274,c_7323,c_7106,c_5963,c_5606,c_5300,c_5055,
% 27.35/4.00                 c_4955,c_4846,c_4526,c_4452,c_4379,c_4378,c_4342,c_4343,
% 27.35/4.00                 c_4344,c_4312,c_3219,c_155,c_151,c_89,c_88,c_86,c_37,
% 27.35/4.00                 c_38,c_39,c_41,c_42,c_43,c_44,c_49,c_46,c_48,c_47]) ).
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.35/4.00  
% 27.35/4.00  ------                               Statistics
% 27.35/4.00  
% 27.35/4.00  ------ General
% 27.35/4.00  
% 27.35/4.00  abstr_ref_over_cycles:                  0
% 27.35/4.00  abstr_ref_under_cycles:                 0
% 27.35/4.00  gc_basic_clause_elim:                   0
% 27.35/4.00  forced_gc_time:                         0
% 27.35/4.00  parsing_time:                           0.01
% 27.35/4.00  unif_index_cands_time:                  0.
% 27.35/4.00  unif_index_add_time:                    0.
% 27.35/4.00  orderings_time:                         0.
% 27.35/4.00  out_proof_time:                         0.024
% 27.35/4.00  total_time:                             3.223
% 27.35/4.00  num_of_symbols:                         58
% 27.35/4.00  num_of_terms:                           56150
% 27.35/4.00  
% 27.35/4.00  ------ Preprocessing
% 27.35/4.00  
% 27.35/4.00  num_of_splits:                          0
% 27.35/4.00  num_of_split_atoms:                     0
% 27.35/4.00  num_of_reused_defs:                     0
% 27.35/4.00  num_eq_ax_congr_red:                    27
% 27.35/4.00  num_of_sem_filtered_clauses:            1
% 27.35/4.00  num_of_subtypes:                        0
% 27.35/4.00  monotx_restored_types:                  0
% 27.35/4.00  sat_num_of_epr_types:                   0
% 27.35/4.00  sat_num_of_non_cyclic_types:            0
% 27.35/4.00  sat_guarded_non_collapsed_types:        0
% 27.35/4.00  num_pure_diseq_elim:                    0
% 27.35/4.00  simp_replaced_by:                       0
% 27.35/4.00  res_preprocessed:                       229
% 27.35/4.00  prep_upred:                             0
% 27.35/4.00  prep_unflattend:                        44
% 27.35/4.00  smt_new_axioms:                         0
% 27.35/4.00  pred_elim_cands:                        11
% 27.35/4.00  pred_elim:                              0
% 27.35/4.00  pred_elim_cl:                           0
% 27.35/4.00  pred_elim_cycles:                       6
% 27.35/4.00  merged_defs:                            16
% 27.35/4.00  merged_defs_ncl:                        0
% 27.35/4.00  bin_hyper_res:                          16
% 27.35/4.00  prep_cycles:                            4
% 27.35/4.00  pred_elim_time:                         0.052
% 27.35/4.00  splitting_time:                         0.
% 27.35/4.00  sem_filter_time:                        0.
% 27.35/4.00  monotx_time:                            0.001
% 27.35/4.00  subtype_inf_time:                       0.
% 27.35/4.00  
% 27.35/4.00  ------ Problem properties
% 27.35/4.00  
% 27.35/4.00  clauses:                                47
% 27.35/4.00  conjectures:                            13
% 27.35/4.00  epr:                                    10
% 27.35/4.00  horn:                                   38
% 27.35/4.00  ground:                                 13
% 27.35/4.00  unary:                                  12
% 27.35/4.00  binary:                                 12
% 27.35/4.00  lits:                                   152
% 27.35/4.00  lits_eq:                                2
% 27.35/4.00  fd_pure:                                0
% 27.35/4.00  fd_pseudo:                              0
% 27.35/4.00  fd_cond:                                0
% 27.35/4.00  fd_pseudo_cond:                         1
% 27.35/4.00  ac_symbols:                             0
% 27.35/4.00  
% 27.35/4.00  ------ Propositional Solver
% 27.35/4.00  
% 27.35/4.00  prop_solver_calls:                      50
% 27.35/4.00  prop_fast_solver_calls:                 12361
% 27.35/4.00  smt_solver_calls:                       0
% 27.35/4.00  smt_fast_solver_calls:                  0
% 27.35/4.00  prop_num_of_clauses:                    26377
% 27.35/4.00  prop_preprocess_simplified:             50608
% 27.35/4.00  prop_fo_subsumed:                       1448
% 27.35/4.00  prop_solver_time:                       0.
% 27.35/4.00  smt_solver_time:                        0.
% 27.35/4.00  smt_fast_solver_time:                   0.
% 27.35/4.00  prop_fast_solver_time:                  0.
% 27.35/4.00  prop_unsat_core_time:                   0.003
% 27.35/4.00  
% 27.35/4.00  ------ QBF
% 27.35/4.00  
% 27.35/4.00  qbf_q_res:                              0
% 27.35/4.00  qbf_num_tautologies:                    0
% 27.35/4.00  qbf_prep_cycles:                        0
% 27.35/4.00  
% 27.35/4.00  ------ BMC1
% 27.35/4.00  
% 27.35/4.00  bmc1_current_bound:                     -1
% 27.35/4.00  bmc1_last_solved_bound:                 -1
% 27.35/4.00  bmc1_unsat_core_size:                   -1
% 27.35/4.00  bmc1_unsat_core_parents_size:           -1
% 27.35/4.00  bmc1_merge_next_fun:                    0
% 27.35/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.35/4.00  
% 27.35/4.00  ------ Instantiation
% 27.35/4.00  
% 27.35/4.00  inst_num_of_clauses:                    2100
% 27.35/4.00  inst_num_in_passive:                    835
% 27.35/4.00  inst_num_in_active:                     3907
% 27.35/4.00  inst_num_in_unprocessed:                146
% 27.35/4.00  inst_num_of_loops:                      4139
% 27.35/4.00  inst_num_of_learning_restarts:          1
% 27.35/4.00  inst_num_moves_active_passive:          213
% 27.35/4.00  inst_lit_activity:                      0
% 27.35/4.00  inst_lit_activity_moves:                0
% 27.35/4.00  inst_num_tautologies:                   0
% 27.35/4.00  inst_num_prop_implied:                  0
% 27.35/4.00  inst_num_existing_simplified:           0
% 27.35/4.00  inst_num_eq_res_simplified:             0
% 27.35/4.00  inst_num_child_elim:                    0
% 27.35/4.00  inst_num_of_dismatching_blockings:      6675
% 27.35/4.00  inst_num_of_non_proper_insts:           12916
% 27.35/4.00  inst_num_of_duplicates:                 0
% 27.35/4.00  inst_inst_num_from_inst_to_res:         0
% 27.35/4.00  inst_dismatching_checking_time:         0.
% 27.35/4.00  
% 27.35/4.00  ------ Resolution
% 27.35/4.00  
% 27.35/4.00  res_num_of_clauses:                     67
% 27.35/4.00  res_num_in_passive:                     67
% 27.35/4.00  res_num_in_active:                      0
% 27.35/4.00  res_num_of_loops:                       233
% 27.35/4.00  res_forward_subset_subsumed:            1107
% 27.35/4.00  res_backward_subset_subsumed:           0
% 27.35/4.00  res_forward_subsumed:                   0
% 27.35/4.00  res_backward_subsumed:                  0
% 27.35/4.00  res_forward_subsumption_resolution:     0
% 27.35/4.00  res_backward_subsumption_resolution:    0
% 27.35/4.00  res_clause_to_clause_subsumption:       15318
% 27.35/4.00  res_orphan_elimination:                 0
% 27.35/4.00  res_tautology_del:                      1594
% 27.35/4.00  res_num_eq_res_simplified:              0
% 27.35/4.00  res_num_sel_changes:                    0
% 27.35/4.00  res_moves_from_active_to_pass:          0
% 27.35/4.00  
% 27.35/4.00  ------ Superposition
% 27.35/4.00  
% 27.35/4.00  sup_time_total:                         0.
% 27.35/4.00  sup_time_generating:                    0.
% 27.35/4.00  sup_time_sim_full:                      0.
% 27.35/4.00  sup_time_sim_immed:                     0.
% 27.35/4.00  
% 27.35/4.00  sup_num_of_clauses:                     2695
% 27.35/4.00  sup_num_in_active:                      759
% 27.35/4.00  sup_num_in_passive:                     1936
% 27.35/4.00  sup_num_of_loops:                       826
% 27.35/4.00  sup_fw_superposition:                   3769
% 27.35/4.00  sup_bw_superposition:                   2115
% 27.35/4.00  sup_immediate_simplified:               3321
% 27.35/4.00  sup_given_eliminated:                   11
% 27.35/4.00  comparisons_done:                       0
% 27.35/4.00  comparisons_avoided:                    0
% 27.35/4.00  
% 27.35/4.00  ------ Simplifications
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  sim_fw_subset_subsumed:                 280
% 27.35/4.00  sim_bw_subset_subsumed:                 63
% 27.35/4.00  sim_fw_subsumed:                        601
% 27.35/4.00  sim_bw_subsumed:                        88
% 27.35/4.00  sim_fw_subsumption_res:                 0
% 27.35/4.00  sim_bw_subsumption_res:                 0
% 27.35/4.00  sim_tautology_del:                      645
% 27.35/4.00  sim_eq_tautology_del:                   263
% 27.35/4.00  sim_eq_res_simp:                        0
% 27.35/4.00  sim_fw_demodulated:                     33
% 27.35/4.00  sim_bw_demodulated:                     14
% 27.35/4.00  sim_light_normalised:                   2838
% 27.35/4.00  sim_joinable_taut:                      0
% 27.35/4.00  sim_joinable_simp:                      0
% 27.35/4.00  sim_ac_normalised:                      0
% 27.35/4.00  sim_smt_subsumption:                    0
% 27.35/4.00  
%------------------------------------------------------------------------------
