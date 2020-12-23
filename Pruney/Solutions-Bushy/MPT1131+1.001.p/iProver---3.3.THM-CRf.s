%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1131+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:57 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  157 (2302 expanded)
%              Number of clauses        :  104 ( 553 expanded)
%              Number of leaves         :   12 ( 693 expanded)
%              Depth                    :   22
%              Number of atoms          :  693 (26950 expanded)
%              Number of equality atoms :  193 (2593 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f31,plain,(
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
     => ( ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
          | v5_pre_topc(X2,X0,X1) )
        & sK4 = X2
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
              | ~ v5_pre_topc(sK3,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
              | v5_pre_topc(sK3,X0,X1) )
            & sK3 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2)
                  | ~ v5_pre_topc(X2,X0,sK2) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2)
                  | v5_pre_topc(X2,X0,sK2) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1)
                    | ~ v5_pre_topc(X2,sK1,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1)
                    | v5_pre_topc(X2,sK1,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
      | ~ v5_pre_topc(sK3,sK1,sK2) )
    & ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
      | v5_pre_topc(sK3,sK1,sK2) )
    & sK3 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f31,f30,f29,f28])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
                    & v4_pre_topc(sK0(X0,X1,X2),X1)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,
    ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v4_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_402,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_23])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v4_pre_topc(X0,sK1) ),
    inference(renaming,[status(thm)],[c_402])).

cnf(c_1108,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v4_pre_topc(X0_47,sK1) ),
    inference(subtyping,[status(esa)],[c_403])).

cnf(c_1839,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v4_pre_topc(X0_47,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1108])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1120,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1827,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1124,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | k8_relset_1(X0_48,X1_48,X0_47,X1_47) = k10_relat_1(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1824,plain,
    ( k8_relset_1(X0_48,X1_48,X0_47,X1_47) = k10_relat_1(X0_47,X1_47)
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1124])).

cnf(c_2322,plain,
    ( k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2),sK4,X0_47) = k10_relat_1(sK4,X0_47) ),
    inference(superposition,[status(thm)],[c_1827,c_1824])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1131,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | v5_pre_topc(X0_47,X0_49,X1_49)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_47,sK0(X0_49,X1_49,X0_47)),X0_49)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1817,plain,
    ( v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | v5_pre_topc(X0_47,X0_49,X1_49) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_47,sK0(X0_49,X1_49,X0_47)),X0_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1131])).

cnf(c_2374,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_1817])).

cnf(c_26,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_28,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_32,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_33,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_52,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_54,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_12,negated_conjecture,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1123,negated_conjecture,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1825,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1123])).

cnf(c_14,negated_conjecture,
    ( sK3 = sK4 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1121,negated_conjecture,
    ( sK3 = sK4 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1879,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1825,c_1121])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1127,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k1_zfmisc_1(X0_48)))
    | l1_pre_topc(g1_pre_topc(X0_48,X0_47)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2060,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0_49),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_49))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_49),u1_pre_topc(X0_49))) ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_2061,plain,
    ( m1_subset_1(u1_pre_topc(X0_49),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_49)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_49),u1_pre_topc(X0_49))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2060])).

cnf(c_2063,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2061])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1117,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1830,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1117])).

cnf(c_1855,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1830,c_1121])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v4_pre_topc(sK0(X1,X2,X0),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1130,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | v5_pre_topc(X0_47,X0_49,X1_49)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v4_pre_topc(sK0(X0_49,X1_49,X0_47),X1_49)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1818,plain,
    ( v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | v5_pre_topc(X0_47,X0_49,X1_49) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | v4_pre_topc(sK0(X0_49,X1_49,X0_47),X1_49) = iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1130])).

cnf(c_2568,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1855,c_1818])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1116,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1831,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1116])).

cnf(c_1852,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1831,c_1121])).

cnf(c_3093,plain,
    ( v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2568,c_26,c_28,c_32,c_1852])).

cnf(c_3094,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3093])).

cnf(c_2323,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0_47) = k10_relat_1(sK4,X0_47) ),
    inference(superposition,[status(thm)],[c_1855,c_1824])).

cnf(c_2371,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_1817])).

cnf(c_3194,plain,
    ( v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2371,c_26,c_28,c_32,c_1852,c_1855])).

cnf(c_3195,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3194])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1129,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | v5_pre_topc(X0_47,X0_49,X1_49)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | m1_subset_1(sK0(X0_49,X1_49,X0_47),k1_zfmisc_1(u1_struct_0(X1_49)))
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1819,plain,
    ( v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | v5_pre_topc(X0_47,X0_49,X1_49) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | m1_subset_1(sK0(X0_49,X1_49,X0_47),k1_zfmisc_1(u1_struct_0(X1_49))) = iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1129])).

cnf(c_2695,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1855,c_1819])).

cnf(c_3138,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2695,c_26,c_28,c_32,c_1852])).

cnf(c_3139,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3138])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1128,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ v5_pre_topc(X0_47,X0_49,X1_49)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(X1_49)))
    | ~ v4_pre_topc(X1_47,X1_49)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_47,X1_47),X0_49)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1820,plain,
    ( v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | v5_pre_topc(X0_47,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(X1_49))) != iProver_top
    | v4_pre_topc(X1_47,X1_49) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_47,X1_47),X0_49) = iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1128])).

cnf(c_2750,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v4_pre_topc(X0_47,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_1820])).

cnf(c_13,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1122,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1826,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1122])).

cnf(c_1870,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1826,c_1121])).

cnf(c_2749,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | v4_pre_topc(X0_47,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_47),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_1820])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1126,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | m1_subset_1(k8_relset_1(X0_48,X1_48,X0_47,X1_47),k1_zfmisc_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1822,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | m1_subset_1(k8_relset_1(X0_48,X1_48,X0_47,X1_47),k1_zfmisc_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1126])).

cnf(c_2598,plain,
    ( m1_subset_1(k10_relat_1(sK4,X0_47),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_1822])).

cnf(c_3304,plain,
    ( m1_subset_1(k10_relat_1(sK4,X0_47),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2598,c_34])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_444,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_23])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(X0,sK1) ),
    inference(renaming,[status(thm)],[c_444])).

cnf(c_1106,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(X0_47,sK1) ),
    inference(subtyping,[status(esa)],[c_445])).

cnf(c_1841,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top
    | v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v4_pre_topc(X0_47,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1106])).

cnf(c_3312,plain,
    ( v4_pre_topc(k10_relat_1(sK4,X0_47),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3304,c_1841])).

cnf(c_3638,plain,
    ( v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top
    | v4_pre_topc(X0_47,sK2) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2750,c_26,c_28,c_32,c_33,c_34,c_54,c_1870,c_1852,c_1855,c_2063,c_2749,c_3312])).

cnf(c_3639,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v4_pre_topc(X0_47,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_3638])).

cnf(c_3649,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3139,c_3639])).

cnf(c_3744,plain,
    ( v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2374,c_26,c_28,c_32,c_33,c_34,c_54,c_1879,c_2063,c_3094,c_3195,c_3649])).

cnf(c_3749,plain,
    ( m1_subset_1(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1839,c_3744])).

cnf(c_2599,plain,
    ( m1_subset_1(k10_relat_1(sK4,X0_47),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_1822])).

cnf(c_3248,plain,
    ( m1_subset_1(k10_relat_1(sK4,X0_47),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2599,c_1855])).

cnf(c_3982,plain,
    ( v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),sK1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3749,c_3248])).

cnf(c_2693,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1827,c_1819])).

cnf(c_3187,plain,
    ( m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2693,c_26,c_28,c_32,c_33,c_54,c_2063])).

cnf(c_3188,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3187])).

cnf(c_3648,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3188,c_3639])).

cnf(c_2567,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1827,c_1818])).

cnf(c_3145,plain,
    ( v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2567,c_26,c_28,c_32,c_33,c_54,c_2063])).

cnf(c_3146,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3145])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3982,c_3649,c_3648,c_3195,c_3146,c_3094,c_1879])).


%------------------------------------------------------------------------------
