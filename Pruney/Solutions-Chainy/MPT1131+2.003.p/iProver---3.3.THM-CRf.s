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
% DateTime   : Thu Dec  3 12:11:46 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :  155 (2297 expanded)
%              Number of clauses        :  102 ( 548 expanded)
%              Number of leaves         :   12 ( 693 expanded)
%              Depth                    :   21
%              Number of atoms          :  688 (26937 expanded)
%              Number of equality atoms :  188 (2580 expanded)
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

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(nnf_transformation,[],[f13])).

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

fof(f38,plain,(
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

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,
    ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f37,plain,(
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

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
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

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_397,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_398,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_23])).

cnf(c_403,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_402])).

cnf(c_1108,plain,
    ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v4_pre_topc(X0_47,sK1)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_403])).

cnf(c_1839,plain,
    ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v4_pre_topc(X0_47,sK1) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
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

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1130,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k8_relset_1(X0_49,X1_49,X0_47,X1_47) = k10_relat_1(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1818,plain,
    ( k8_relset_1(X0_49,X1_49,X0_47,X1_47) = k10_relat_1(X0_47,X1_47)
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1130])).

cnf(c_2321,plain,
    ( k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2),sK4,X0_47) = k10_relat_1(sK4,X0_47) ),
    inference(superposition,[status(thm)],[c_1827,c_1818])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1129,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | v5_pre_topc(X0_47,X0_48,X1_48)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,sK0(X0_48,X1_48,X0_47)),X0_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ l1_pre_topc(X0_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1819,plain,
    ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v5_pre_topc(X0_47,X0_48,X1_48) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,sK0(X0_48,X1_48,X0_47)),X0_48) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1129])).

cnf(c_2572,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_1819])).

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

cnf(c_7,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_49,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_51,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

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

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1125,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k1_zfmisc_1(X0_49)))
    | l1_pre_topc(g1_pre_topc(X0_49,X0_47)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2060,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_48))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_48),u1_pre_topc(X0_48))) ),
    inference(instantiation,[status(thm)],[c_1125])).

cnf(c_2061,plain,
    ( m1_subset_1(u1_pre_topc(X0_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_48)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_48),u1_pre_topc(X0_48))) = iProver_top ),
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

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v4_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1128,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | v5_pre_topc(X0_47,X0_48,X1_48)
    | v4_pre_topc(sK0(X0_48,X1_48,X0_47),X1_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ l1_pre_topc(X0_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1820,plain,
    ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v5_pre_topc(X0_47,X0_48,X1_48) = iProver_top
    | v4_pre_topc(sK0(X0_48,X1_48,X0_47),X1_48) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1128])).

cnf(c_2652,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1855,c_1820])).

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

cnf(c_3141,plain,
    ( v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2652,c_26,c_28,c_32,c_1852])).

cnf(c_3142,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3141])).

cnf(c_2323,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0_47) = k10_relat_1(sK4,X0_47) ),
    inference(superposition,[status(thm)],[c_1855,c_1818])).

cnf(c_2573,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_1819])).

cnf(c_3679,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2573,c_26,c_28,c_32,c_1852,c_1855])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1127,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | v5_pre_topc(X0_47,X0_48,X1_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | m1_subset_1(sK0(X0_48,X1_48,X0_47),k1_zfmisc_1(u1_struct_0(X1_48)))
    | ~ l1_pre_topc(X0_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1821,plain,
    ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v5_pre_topc(X0_47,X0_48,X1_48) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_subset_1(sK0(X0_48,X1_48,X0_47),k1_zfmisc_1(u1_struct_0(X1_48))) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1127])).

cnf(c_2743,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1855,c_1821])).

cnf(c_3186,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2743,c_26,c_28,c_32,c_1852])).

cnf(c_3187,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3186])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1126,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ v5_pre_topc(X0_47,X0_48,X1_48)
    | ~ v4_pre_topc(X1_47,X1_48)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,X1_47),X0_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(X1_48)))
    | ~ l1_pre_topc(X0_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1822,plain,
    ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v5_pre_topc(X0_47,X0_48,X1_48) != iProver_top
    | v4_pre_topc(X1_47,X1_48) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,X1_47),X0_48) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(X1_48))) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1126])).

cnf(c_2798,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top
    | v4_pre_topc(X0_47,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_1822])).

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

cnf(c_2797,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | v4_pre_topc(X0_47,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_47),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_1822])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1131,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | m1_subset_1(k8_relset_1(X0_49,X1_49,X0_47,X1_47),k1_zfmisc_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1817,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(k8_relset_1(X0_49,X1_49,X0_47,X1_47),k1_zfmisc_1(X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1131])).

cnf(c_2383,plain,
    ( m1_subset_1(k10_relat_1(sK4,X0_47),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_1817])).

cnf(c_3300,plain,
    ( m1_subset_1(k10_relat_1(sK4,X0_47),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2383,c_34])).

cnf(c_9,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_439,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_440,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_23])).

cnf(c_445,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(renaming,[status(thm)],[c_444])).

cnf(c_1106,plain,
    ( ~ v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(X0_47,sK1)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(subtyping,[status(esa)],[c_445])).

cnf(c_1841,plain,
    ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v4_pre_topc(X0_47,sK1) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1106])).

cnf(c_3308,plain,
    ( v4_pre_topc(k10_relat_1(sK4,X0_47),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3300,c_1841])).

cnf(c_3686,plain,
    ( v4_pre_topc(X0_47,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2798,c_26,c_28,c_32,c_33,c_34,c_51,c_1870,c_1852,c_1855,c_2063,c_2797,c_3308])).

cnf(c_3697,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3187,c_3686])).

cnf(c_3792,plain,
    ( v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2572,c_26,c_28,c_32,c_33,c_34,c_51,c_1879,c_2063,c_3142,c_3679,c_3697])).

cnf(c_3797,plain,
    ( v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),sK1) != iProver_top
    | m1_subset_1(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1839,c_3792])).

cnf(c_2378,plain,
    ( m1_subset_1(k10_relat_1(sK4,X0_47),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_1817])).

cnf(c_3292,plain,
    ( m1_subset_1(k10_relat_1(sK4,X0_47),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2378,c_1855])).

cnf(c_4032,plain,
    ( v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),sK1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3797,c_3292])).

cnf(c_2741,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1827,c_1821])).

cnf(c_3235,plain,
    ( m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2741,c_26,c_28,c_32,c_33,c_51,c_2063])).

cnf(c_3236,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3235])).

cnf(c_3696,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3236,c_3686])).

cnf(c_2650,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1827,c_1820])).

cnf(c_3193,plain,
    ( v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2650,c_26,c_28,c_32,c_33,c_51,c_2063])).

cnf(c_3194,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3193])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4032,c_3697,c_3696,c_3679,c_3194,c_3142,c_1879])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:06:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.39/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.05  
% 2.39/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.39/1.05  
% 2.39/1.05  ------  iProver source info
% 2.39/1.05  
% 2.39/1.05  git: date: 2020-06-30 10:37:57 +0100
% 2.39/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.39/1.05  git: non_committed_changes: false
% 2.39/1.05  git: last_make_outside_of_git: false
% 2.39/1.05  
% 2.39/1.05  ------ 
% 2.39/1.05  
% 2.39/1.05  ------ Input Options
% 2.39/1.05  
% 2.39/1.05  --out_options                           all
% 2.39/1.05  --tptp_safe_out                         true
% 2.39/1.05  --problem_path                          ""
% 2.39/1.05  --include_path                          ""
% 2.39/1.05  --clausifier                            res/vclausify_rel
% 2.39/1.05  --clausifier_options                    --mode clausify
% 2.39/1.05  --stdin                                 false
% 2.39/1.05  --stats_out                             all
% 2.39/1.05  
% 2.39/1.05  ------ General Options
% 2.39/1.05  
% 2.39/1.05  --fof                                   false
% 2.39/1.05  --time_out_real                         305.
% 2.39/1.05  --time_out_virtual                      -1.
% 2.39/1.05  --symbol_type_check                     false
% 2.39/1.05  --clausify_out                          false
% 2.39/1.05  --sig_cnt_out                           false
% 2.39/1.05  --trig_cnt_out                          false
% 2.39/1.05  --trig_cnt_out_tolerance                1.
% 2.39/1.05  --trig_cnt_out_sk_spl                   false
% 2.39/1.05  --abstr_cl_out                          false
% 2.39/1.05  
% 2.39/1.05  ------ Global Options
% 2.39/1.05  
% 2.39/1.05  --schedule                              default
% 2.39/1.05  --add_important_lit                     false
% 2.39/1.05  --prop_solver_per_cl                    1000
% 2.39/1.05  --min_unsat_core                        false
% 2.39/1.05  --soft_assumptions                      false
% 2.39/1.05  --soft_lemma_size                       3
% 2.39/1.05  --prop_impl_unit_size                   0
% 2.39/1.05  --prop_impl_unit                        []
% 2.39/1.05  --share_sel_clauses                     true
% 2.39/1.05  --reset_solvers                         false
% 2.39/1.05  --bc_imp_inh                            [conj_cone]
% 2.39/1.05  --conj_cone_tolerance                   3.
% 2.39/1.05  --extra_neg_conj                        none
% 2.39/1.05  --large_theory_mode                     true
% 2.39/1.05  --prolific_symb_bound                   200
% 2.39/1.05  --lt_threshold                          2000
% 2.39/1.05  --clause_weak_htbl                      true
% 2.39/1.05  --gc_record_bc_elim                     false
% 2.39/1.05  
% 2.39/1.05  ------ Preprocessing Options
% 2.39/1.05  
% 2.39/1.05  --preprocessing_flag                    true
% 2.39/1.05  --time_out_prep_mult                    0.1
% 2.39/1.05  --splitting_mode                        input
% 2.39/1.05  --splitting_grd                         true
% 2.39/1.05  --splitting_cvd                         false
% 2.39/1.05  --splitting_cvd_svl                     false
% 2.39/1.05  --splitting_nvd                         32
% 2.39/1.05  --sub_typing                            true
% 2.39/1.05  --prep_gs_sim                           true
% 2.39/1.05  --prep_unflatten                        true
% 2.39/1.05  --prep_res_sim                          true
% 2.39/1.05  --prep_upred                            true
% 2.39/1.05  --prep_sem_filter                       exhaustive
% 2.39/1.05  --prep_sem_filter_out                   false
% 2.39/1.05  --pred_elim                             true
% 2.39/1.05  --res_sim_input                         true
% 2.39/1.05  --eq_ax_congr_red                       true
% 2.39/1.05  --pure_diseq_elim                       true
% 2.39/1.05  --brand_transform                       false
% 2.39/1.05  --non_eq_to_eq                          false
% 2.39/1.05  --prep_def_merge                        true
% 2.39/1.05  --prep_def_merge_prop_impl              false
% 2.39/1.05  --prep_def_merge_mbd                    true
% 2.39/1.05  --prep_def_merge_tr_red                 false
% 2.39/1.05  --prep_def_merge_tr_cl                  false
% 2.39/1.05  --smt_preprocessing                     true
% 2.39/1.05  --smt_ac_axioms                         fast
% 2.39/1.05  --preprocessed_out                      false
% 2.39/1.05  --preprocessed_stats                    false
% 2.39/1.05  
% 2.39/1.05  ------ Abstraction refinement Options
% 2.39/1.05  
% 2.39/1.05  --abstr_ref                             []
% 2.39/1.05  --abstr_ref_prep                        false
% 2.39/1.05  --abstr_ref_until_sat                   false
% 2.39/1.05  --abstr_ref_sig_restrict                funpre
% 2.39/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.39/1.05  --abstr_ref_under                       []
% 2.39/1.05  
% 2.39/1.05  ------ SAT Options
% 2.39/1.05  
% 2.39/1.05  --sat_mode                              false
% 2.39/1.05  --sat_fm_restart_options                ""
% 2.39/1.05  --sat_gr_def                            false
% 2.39/1.05  --sat_epr_types                         true
% 2.39/1.05  --sat_non_cyclic_types                  false
% 2.39/1.05  --sat_finite_models                     false
% 2.39/1.05  --sat_fm_lemmas                         false
% 2.39/1.05  --sat_fm_prep                           false
% 2.39/1.05  --sat_fm_uc_incr                        true
% 2.39/1.05  --sat_out_model                         small
% 2.39/1.05  --sat_out_clauses                       false
% 2.39/1.05  
% 2.39/1.05  ------ QBF Options
% 2.39/1.05  
% 2.39/1.05  --qbf_mode                              false
% 2.39/1.05  --qbf_elim_univ                         false
% 2.39/1.05  --qbf_dom_inst                          none
% 2.39/1.05  --qbf_dom_pre_inst                      false
% 2.39/1.05  --qbf_sk_in                             false
% 2.39/1.05  --qbf_pred_elim                         true
% 2.39/1.05  --qbf_split                             512
% 2.39/1.05  
% 2.39/1.05  ------ BMC1 Options
% 2.39/1.05  
% 2.39/1.05  --bmc1_incremental                      false
% 2.39/1.05  --bmc1_axioms                           reachable_all
% 2.39/1.05  --bmc1_min_bound                        0
% 2.39/1.05  --bmc1_max_bound                        -1
% 2.39/1.05  --bmc1_max_bound_default                -1
% 2.39/1.05  --bmc1_symbol_reachability              true
% 2.39/1.05  --bmc1_property_lemmas                  false
% 2.39/1.05  --bmc1_k_induction                      false
% 2.39/1.05  --bmc1_non_equiv_states                 false
% 2.39/1.05  --bmc1_deadlock                         false
% 2.39/1.05  --bmc1_ucm                              false
% 2.39/1.05  --bmc1_add_unsat_core                   none
% 2.39/1.05  --bmc1_unsat_core_children              false
% 2.39/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.39/1.05  --bmc1_out_stat                         full
% 2.39/1.05  --bmc1_ground_init                      false
% 2.39/1.05  --bmc1_pre_inst_next_state              false
% 2.39/1.05  --bmc1_pre_inst_state                   false
% 2.39/1.05  --bmc1_pre_inst_reach_state             false
% 2.39/1.05  --bmc1_out_unsat_core                   false
% 2.39/1.05  --bmc1_aig_witness_out                  false
% 2.39/1.05  --bmc1_verbose                          false
% 2.39/1.05  --bmc1_dump_clauses_tptp                false
% 2.39/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.39/1.05  --bmc1_dump_file                        -
% 2.39/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.39/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.39/1.05  --bmc1_ucm_extend_mode                  1
% 2.39/1.05  --bmc1_ucm_init_mode                    2
% 2.39/1.05  --bmc1_ucm_cone_mode                    none
% 2.39/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.39/1.05  --bmc1_ucm_relax_model                  4
% 2.39/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.39/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.39/1.05  --bmc1_ucm_layered_model                none
% 2.39/1.05  --bmc1_ucm_max_lemma_size               10
% 2.39/1.05  
% 2.39/1.05  ------ AIG Options
% 2.39/1.05  
% 2.39/1.05  --aig_mode                              false
% 2.39/1.05  
% 2.39/1.05  ------ Instantiation Options
% 2.39/1.05  
% 2.39/1.05  --instantiation_flag                    true
% 2.39/1.05  --inst_sos_flag                         false
% 2.39/1.05  --inst_sos_phase                        true
% 2.39/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.39/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.39/1.05  --inst_lit_sel_side                     num_symb
% 2.39/1.05  --inst_solver_per_active                1400
% 2.39/1.05  --inst_solver_calls_frac                1.
% 2.39/1.05  --inst_passive_queue_type               priority_queues
% 2.39/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.39/1.05  --inst_passive_queues_freq              [25;2]
% 2.39/1.05  --inst_dismatching                      true
% 2.39/1.05  --inst_eager_unprocessed_to_passive     true
% 2.39/1.05  --inst_prop_sim_given                   true
% 2.39/1.05  --inst_prop_sim_new                     false
% 2.39/1.05  --inst_subs_new                         false
% 2.39/1.05  --inst_eq_res_simp                      false
% 2.39/1.05  --inst_subs_given                       false
% 2.39/1.05  --inst_orphan_elimination               true
% 2.39/1.05  --inst_learning_loop_flag               true
% 2.39/1.05  --inst_learning_start                   3000
% 2.39/1.05  --inst_learning_factor                  2
% 2.39/1.05  --inst_start_prop_sim_after_learn       3
% 2.39/1.05  --inst_sel_renew                        solver
% 2.39/1.05  --inst_lit_activity_flag                true
% 2.39/1.05  --inst_restr_to_given                   false
% 2.39/1.05  --inst_activity_threshold               500
% 2.39/1.05  --inst_out_proof                        true
% 2.39/1.05  
% 2.39/1.05  ------ Resolution Options
% 2.39/1.05  
% 2.39/1.05  --resolution_flag                       true
% 2.39/1.05  --res_lit_sel                           adaptive
% 2.39/1.05  --res_lit_sel_side                      none
% 2.39/1.05  --res_ordering                          kbo
% 2.39/1.05  --res_to_prop_solver                    active
% 2.39/1.05  --res_prop_simpl_new                    false
% 2.39/1.05  --res_prop_simpl_given                  true
% 2.39/1.05  --res_passive_queue_type                priority_queues
% 2.39/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.39/1.05  --res_passive_queues_freq               [15;5]
% 2.39/1.05  --res_forward_subs                      full
% 2.39/1.05  --res_backward_subs                     full
% 2.39/1.05  --res_forward_subs_resolution           true
% 2.39/1.05  --res_backward_subs_resolution          true
% 2.39/1.05  --res_orphan_elimination                true
% 2.39/1.05  --res_time_limit                        2.
% 2.39/1.05  --res_out_proof                         true
% 2.39/1.05  
% 2.39/1.05  ------ Superposition Options
% 2.39/1.05  
% 2.39/1.05  --superposition_flag                    true
% 2.39/1.05  --sup_passive_queue_type                priority_queues
% 2.39/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.39/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.39/1.05  --demod_completeness_check              fast
% 2.39/1.05  --demod_use_ground                      true
% 2.39/1.05  --sup_to_prop_solver                    passive
% 2.39/1.05  --sup_prop_simpl_new                    true
% 2.39/1.05  --sup_prop_simpl_given                  true
% 2.39/1.05  --sup_fun_splitting                     false
% 2.39/1.05  --sup_smt_interval                      50000
% 2.39/1.05  
% 2.39/1.05  ------ Superposition Simplification Setup
% 2.39/1.05  
% 2.39/1.05  --sup_indices_passive                   []
% 2.39/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.39/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.05  --sup_full_bw                           [BwDemod]
% 2.39/1.05  --sup_immed_triv                        [TrivRules]
% 2.39/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.39/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.05  --sup_immed_bw_main                     []
% 2.39/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.39/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.06  
% 2.39/1.06  ------ Combination Options
% 2.39/1.06  
% 2.39/1.06  --comb_res_mult                         3
% 2.39/1.06  --comb_sup_mult                         2
% 2.39/1.06  --comb_inst_mult                        10
% 2.39/1.06  
% 2.39/1.06  ------ Debug Options
% 2.39/1.06  
% 2.39/1.06  --dbg_backtrace                         false
% 2.39/1.06  --dbg_dump_prop_clauses                 false
% 2.39/1.06  --dbg_dump_prop_clauses_file            -
% 2.39/1.06  --dbg_out_stat                          false
% 2.39/1.06  ------ Parsing...
% 2.39/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.39/1.06  
% 2.39/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 2.39/1.06  
% 2.39/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.39/1.06  
% 2.39/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.39/1.06  ------ Proving...
% 2.39/1.06  ------ Problem Properties 
% 2.39/1.06  
% 2.39/1.06  
% 2.39/1.06  clauses                                 27
% 2.39/1.06  conjectures                             11
% 2.39/1.06  EPR                                     5
% 2.39/1.06  Horn                                    24
% 2.39/1.06  unary                                   9
% 2.39/1.06  binary                                  6
% 2.39/1.06  lits                                    75
% 2.39/1.06  lits eq                                 2
% 2.39/1.06  fd_pure                                 0
% 2.39/1.06  fd_pseudo                               0
% 2.39/1.06  fd_cond                                 0
% 2.39/1.06  fd_pseudo_cond                          0
% 2.39/1.06  AC symbols                              0
% 2.39/1.06  
% 2.39/1.06  ------ Schedule dynamic 5 is on 
% 2.39/1.06  
% 2.39/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.39/1.06  
% 2.39/1.06  
% 2.39/1.06  ------ 
% 2.39/1.06  Current options:
% 2.39/1.06  ------ 
% 2.39/1.06  
% 2.39/1.06  ------ Input Options
% 2.39/1.06  
% 2.39/1.06  --out_options                           all
% 2.39/1.06  --tptp_safe_out                         true
% 2.39/1.06  --problem_path                          ""
% 2.39/1.06  --include_path                          ""
% 2.39/1.06  --clausifier                            res/vclausify_rel
% 2.39/1.06  --clausifier_options                    --mode clausify
% 2.39/1.06  --stdin                                 false
% 2.39/1.06  --stats_out                             all
% 2.39/1.06  
% 2.39/1.06  ------ General Options
% 2.39/1.06  
% 2.39/1.06  --fof                                   false
% 2.39/1.06  --time_out_real                         305.
% 2.39/1.06  --time_out_virtual                      -1.
% 2.39/1.06  --symbol_type_check                     false
% 2.39/1.06  --clausify_out                          false
% 2.39/1.06  --sig_cnt_out                           false
% 2.39/1.06  --trig_cnt_out                          false
% 2.39/1.06  --trig_cnt_out_tolerance                1.
% 2.39/1.06  --trig_cnt_out_sk_spl                   false
% 2.39/1.06  --abstr_cl_out                          false
% 2.39/1.06  
% 2.39/1.06  ------ Global Options
% 2.39/1.06  
% 2.39/1.06  --schedule                              default
% 2.39/1.06  --add_important_lit                     false
% 2.39/1.06  --prop_solver_per_cl                    1000
% 2.39/1.06  --min_unsat_core                        false
% 2.39/1.06  --soft_assumptions                      false
% 2.39/1.06  --soft_lemma_size                       3
% 2.39/1.06  --prop_impl_unit_size                   0
% 2.39/1.06  --prop_impl_unit                        []
% 2.39/1.06  --share_sel_clauses                     true
% 2.39/1.06  --reset_solvers                         false
% 2.39/1.06  --bc_imp_inh                            [conj_cone]
% 2.39/1.06  --conj_cone_tolerance                   3.
% 2.39/1.06  --extra_neg_conj                        none
% 2.39/1.06  --large_theory_mode                     true
% 2.39/1.06  --prolific_symb_bound                   200
% 2.39/1.06  --lt_threshold                          2000
% 2.39/1.06  --clause_weak_htbl                      true
% 2.39/1.06  --gc_record_bc_elim                     false
% 2.39/1.06  
% 2.39/1.06  ------ Preprocessing Options
% 2.39/1.06  
% 2.39/1.06  --preprocessing_flag                    true
% 2.39/1.06  --time_out_prep_mult                    0.1
% 2.39/1.06  --splitting_mode                        input
% 2.39/1.06  --splitting_grd                         true
% 2.39/1.06  --splitting_cvd                         false
% 2.39/1.06  --splitting_cvd_svl                     false
% 2.39/1.06  --splitting_nvd                         32
% 2.39/1.06  --sub_typing                            true
% 2.39/1.06  --prep_gs_sim                           true
% 2.39/1.06  --prep_unflatten                        true
% 2.39/1.06  --prep_res_sim                          true
% 2.39/1.06  --prep_upred                            true
% 2.39/1.06  --prep_sem_filter                       exhaustive
% 2.39/1.06  --prep_sem_filter_out                   false
% 2.39/1.06  --pred_elim                             true
% 2.39/1.06  --res_sim_input                         true
% 2.39/1.06  --eq_ax_congr_red                       true
% 2.39/1.06  --pure_diseq_elim                       true
% 2.39/1.06  --brand_transform                       false
% 2.39/1.06  --non_eq_to_eq                          false
% 2.39/1.06  --prep_def_merge                        true
% 2.39/1.06  --prep_def_merge_prop_impl              false
% 2.39/1.06  --prep_def_merge_mbd                    true
% 2.39/1.06  --prep_def_merge_tr_red                 false
% 2.39/1.06  --prep_def_merge_tr_cl                  false
% 2.39/1.06  --smt_preprocessing                     true
% 2.39/1.06  --smt_ac_axioms                         fast
% 2.39/1.06  --preprocessed_out                      false
% 2.39/1.06  --preprocessed_stats                    false
% 2.39/1.06  
% 2.39/1.06  ------ Abstraction refinement Options
% 2.39/1.06  
% 2.39/1.06  --abstr_ref                             []
% 2.39/1.06  --abstr_ref_prep                        false
% 2.39/1.06  --abstr_ref_until_sat                   false
% 2.39/1.06  --abstr_ref_sig_restrict                funpre
% 2.39/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.39/1.06  --abstr_ref_under                       []
% 2.39/1.06  
% 2.39/1.06  ------ SAT Options
% 2.39/1.06  
% 2.39/1.06  --sat_mode                              false
% 2.39/1.06  --sat_fm_restart_options                ""
% 2.39/1.06  --sat_gr_def                            false
% 2.39/1.06  --sat_epr_types                         true
% 2.39/1.06  --sat_non_cyclic_types                  false
% 2.39/1.06  --sat_finite_models                     false
% 2.39/1.06  --sat_fm_lemmas                         false
% 2.39/1.06  --sat_fm_prep                           false
% 2.39/1.06  --sat_fm_uc_incr                        true
% 2.39/1.06  --sat_out_model                         small
% 2.39/1.06  --sat_out_clauses                       false
% 2.39/1.06  
% 2.39/1.06  ------ QBF Options
% 2.39/1.06  
% 2.39/1.06  --qbf_mode                              false
% 2.39/1.06  --qbf_elim_univ                         false
% 2.39/1.06  --qbf_dom_inst                          none
% 2.39/1.06  --qbf_dom_pre_inst                      false
% 2.39/1.06  --qbf_sk_in                             false
% 2.39/1.06  --qbf_pred_elim                         true
% 2.39/1.06  --qbf_split                             512
% 2.39/1.06  
% 2.39/1.06  ------ BMC1 Options
% 2.39/1.06  
% 2.39/1.06  --bmc1_incremental                      false
% 2.39/1.06  --bmc1_axioms                           reachable_all
% 2.39/1.06  --bmc1_min_bound                        0
% 2.39/1.06  --bmc1_max_bound                        -1
% 2.39/1.06  --bmc1_max_bound_default                -1
% 2.39/1.06  --bmc1_symbol_reachability              true
% 2.39/1.06  --bmc1_property_lemmas                  false
% 2.39/1.06  --bmc1_k_induction                      false
% 2.39/1.06  --bmc1_non_equiv_states                 false
% 2.39/1.06  --bmc1_deadlock                         false
% 2.39/1.06  --bmc1_ucm                              false
% 2.39/1.06  --bmc1_add_unsat_core                   none
% 2.39/1.06  --bmc1_unsat_core_children              false
% 2.39/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.39/1.06  --bmc1_out_stat                         full
% 2.39/1.06  --bmc1_ground_init                      false
% 2.39/1.06  --bmc1_pre_inst_next_state              false
% 2.39/1.06  --bmc1_pre_inst_state                   false
% 2.39/1.06  --bmc1_pre_inst_reach_state             false
% 2.39/1.06  --bmc1_out_unsat_core                   false
% 2.39/1.06  --bmc1_aig_witness_out                  false
% 2.39/1.06  --bmc1_verbose                          false
% 2.39/1.06  --bmc1_dump_clauses_tptp                false
% 2.39/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.39/1.06  --bmc1_dump_file                        -
% 2.39/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.39/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.39/1.06  --bmc1_ucm_extend_mode                  1
% 2.39/1.06  --bmc1_ucm_init_mode                    2
% 2.39/1.06  --bmc1_ucm_cone_mode                    none
% 2.39/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.39/1.06  --bmc1_ucm_relax_model                  4
% 2.39/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.39/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.39/1.06  --bmc1_ucm_layered_model                none
% 2.39/1.06  --bmc1_ucm_max_lemma_size               10
% 2.39/1.06  
% 2.39/1.06  ------ AIG Options
% 2.39/1.06  
% 2.39/1.06  --aig_mode                              false
% 2.39/1.06  
% 2.39/1.06  ------ Instantiation Options
% 2.39/1.06  
% 2.39/1.06  --instantiation_flag                    true
% 2.39/1.06  --inst_sos_flag                         false
% 2.39/1.06  --inst_sos_phase                        true
% 2.39/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.39/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.39/1.06  --inst_lit_sel_side                     none
% 2.39/1.06  --inst_solver_per_active                1400
% 2.39/1.06  --inst_solver_calls_frac                1.
% 2.39/1.06  --inst_passive_queue_type               priority_queues
% 2.39/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.39/1.06  --inst_passive_queues_freq              [25;2]
% 2.39/1.06  --inst_dismatching                      true
% 2.39/1.06  --inst_eager_unprocessed_to_passive     true
% 2.39/1.06  --inst_prop_sim_given                   true
% 2.39/1.06  --inst_prop_sim_new                     false
% 2.39/1.06  --inst_subs_new                         false
% 2.39/1.06  --inst_eq_res_simp                      false
% 2.39/1.06  --inst_subs_given                       false
% 2.39/1.06  --inst_orphan_elimination               true
% 2.39/1.06  --inst_learning_loop_flag               true
% 2.39/1.06  --inst_learning_start                   3000
% 2.39/1.06  --inst_learning_factor                  2
% 2.39/1.06  --inst_start_prop_sim_after_learn       3
% 2.39/1.06  --inst_sel_renew                        solver
% 2.39/1.06  --inst_lit_activity_flag                true
% 2.39/1.06  --inst_restr_to_given                   false
% 2.39/1.06  --inst_activity_threshold               500
% 2.39/1.06  --inst_out_proof                        true
% 2.39/1.06  
% 2.39/1.06  ------ Resolution Options
% 2.39/1.06  
% 2.39/1.06  --resolution_flag                       false
% 2.39/1.06  --res_lit_sel                           adaptive
% 2.39/1.06  --res_lit_sel_side                      none
% 2.39/1.06  --res_ordering                          kbo
% 2.39/1.06  --res_to_prop_solver                    active
% 2.39/1.06  --res_prop_simpl_new                    false
% 2.39/1.06  --res_prop_simpl_given                  true
% 2.39/1.06  --res_passive_queue_type                priority_queues
% 2.39/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.39/1.06  --res_passive_queues_freq               [15;5]
% 2.39/1.06  --res_forward_subs                      full
% 2.39/1.06  --res_backward_subs                     full
% 2.39/1.06  --res_forward_subs_resolution           true
% 2.39/1.06  --res_backward_subs_resolution          true
% 2.39/1.06  --res_orphan_elimination                true
% 2.39/1.06  --res_time_limit                        2.
% 2.39/1.06  --res_out_proof                         true
% 2.39/1.06  
% 2.39/1.06  ------ Superposition Options
% 2.39/1.06  
% 2.39/1.06  --superposition_flag                    true
% 2.39/1.06  --sup_passive_queue_type                priority_queues
% 2.39/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.39/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.39/1.06  --demod_completeness_check              fast
% 2.39/1.06  --demod_use_ground                      true
% 2.39/1.06  --sup_to_prop_solver                    passive
% 2.39/1.06  --sup_prop_simpl_new                    true
% 2.39/1.06  --sup_prop_simpl_given                  true
% 2.39/1.06  --sup_fun_splitting                     false
% 2.39/1.06  --sup_smt_interval                      50000
% 2.39/1.06  
% 2.39/1.06  ------ Superposition Simplification Setup
% 2.39/1.06  
% 2.39/1.06  --sup_indices_passive                   []
% 2.39/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.39/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.06  --sup_full_bw                           [BwDemod]
% 2.39/1.06  --sup_immed_triv                        [TrivRules]
% 2.39/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.39/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.06  --sup_immed_bw_main                     []
% 2.39/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.39/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.06  
% 2.39/1.06  ------ Combination Options
% 2.39/1.06  
% 2.39/1.06  --comb_res_mult                         3
% 2.39/1.06  --comb_sup_mult                         2
% 2.39/1.06  --comb_inst_mult                        10
% 2.39/1.06  
% 2.39/1.06  ------ Debug Options
% 2.39/1.06  
% 2.39/1.06  --dbg_backtrace                         false
% 2.39/1.06  --dbg_dump_prop_clauses                 false
% 2.39/1.06  --dbg_dump_prop_clauses_file            -
% 2.39/1.06  --dbg_out_stat                          false
% 2.39/1.06  
% 2.39/1.06  
% 2.39/1.06  
% 2.39/1.06  
% 2.39/1.06  ------ Proving...
% 2.39/1.06  
% 2.39/1.06  
% 2.39/1.06  % SZS status Theorem for theBenchmark.p
% 2.39/1.06  
% 2.39/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 2.39/1.06  
% 2.39/1.06  fof(f6,axiom,(
% 2.39/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.39/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/1.06  
% 2.39/1.06  fof(f16,plain,(
% 2.39/1.06    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.39/1.06    inference(ennf_transformation,[],[f6])).
% 2.39/1.06  
% 2.39/1.06  fof(f17,plain,(
% 2.39/1.06    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.39/1.06    inference(flattening,[],[f16])).
% 2.39/1.06  
% 2.39/1.06  fof(f24,plain,(
% 2.39/1.06    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.39/1.06    inference(nnf_transformation,[],[f17])).
% 2.39/1.06  
% 2.39/1.06  fof(f25,plain,(
% 2.39/1.06    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.39/1.06    inference(flattening,[],[f24])).
% 2.39/1.06  
% 2.39/1.06  fof(f41,plain,(
% 2.39/1.06    ( ! [X0,X1] : (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.39/1.06    inference(cnf_transformation,[],[f25])).
% 2.39/1.06  
% 2.39/1.06  fof(f7,conjecture,(
% 2.39/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.39/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/1.06  
% 2.39/1.06  fof(f8,negated_conjecture,(
% 2.39/1.06    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.39/1.06    inference(negated_conjecture,[],[f7])).
% 2.39/1.06  
% 2.39/1.06  fof(f18,plain,(
% 2.39/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.39/1.06    inference(ennf_transformation,[],[f8])).
% 2.39/1.06  
% 2.39/1.06  fof(f19,plain,(
% 2.39/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.39/1.06    inference(flattening,[],[f18])).
% 2.39/1.06  
% 2.39/1.06  fof(f26,plain,(
% 2.39/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.39/1.06    inference(nnf_transformation,[],[f19])).
% 2.39/1.06  
% 2.39/1.06  fof(f27,plain,(
% 2.39/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.39/1.06    inference(flattening,[],[f26])).
% 2.39/1.06  
% 2.39/1.06  fof(f31,plain,(
% 2.39/1.06    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => ((~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & sK4 = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.39/1.06    introduced(choice_axiom,[])).
% 2.39/1.06  
% 2.39/1.06  fof(f30,plain,(
% 2.39/1.06    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(sK3,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(sK3,X0,X1)) & sK3 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 2.39/1.06    introduced(choice_axiom,[])).
% 2.39/1.06  
% 2.39/1.06  fof(f29,plain,(
% 2.39/1.06    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) | ~v5_pre_topc(X2,X0,sK2)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) | v5_pre_topc(X2,X0,sK2)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))) )),
% 2.39/1.06    introduced(choice_axiom,[])).
% 2.39/1.06  
% 2.39/1.06  fof(f28,plain,(
% 2.39/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) | ~v5_pre_topc(X2,sK1,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) | v5_pre_topc(X2,sK1,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.39/1.06    introduced(choice_axiom,[])).
% 2.39/1.06  
% 2.39/1.06  fof(f32,plain,(
% 2.39/1.06    ((((~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v5_pre_topc(sK3,sK1,sK2)) & (v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | v5_pre_topc(sK3,sK1,sK2)) & sK3 = sK4 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 2.39/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f31,f30,f29,f28])).
% 2.39/1.06  
% 2.39/1.06  fof(f45,plain,(
% 2.39/1.06    v2_pre_topc(sK1)),
% 2.39/1.06    inference(cnf_transformation,[],[f32])).
% 2.39/1.06  
% 2.39/1.06  fof(f46,plain,(
% 2.39/1.06    l1_pre_topc(sK1)),
% 2.39/1.06    inference(cnf_transformation,[],[f32])).
% 2.39/1.06  
% 2.39/1.06  fof(f54,plain,(
% 2.39/1.06    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))),
% 2.39/1.06    inference(cnf_transformation,[],[f32])).
% 2.39/1.06  
% 2.39/1.06  fof(f2,axiom,(
% 2.39/1.06    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 2.39/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/1.06  
% 2.39/1.06  fof(f11,plain,(
% 2.39/1.06    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.39/1.06    inference(ennf_transformation,[],[f2])).
% 2.39/1.06  
% 2.39/1.06  fof(f34,plain,(
% 2.39/1.06    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.39/1.06    inference(cnf_transformation,[],[f11])).
% 2.39/1.06  
% 2.39/1.06  fof(f3,axiom,(
% 2.39/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 2.39/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/1.06  
% 2.39/1.06  fof(f12,plain,(
% 2.39/1.06    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.39/1.06    inference(ennf_transformation,[],[f3])).
% 2.39/1.06  
% 2.39/1.06  fof(f13,plain,(
% 2.39/1.06    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.39/1.06    inference(flattening,[],[f12])).
% 2.39/1.06  
% 2.39/1.06  fof(f20,plain,(
% 2.39/1.06    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.39/1.06    inference(nnf_transformation,[],[f13])).
% 2.39/1.06  
% 2.39/1.06  fof(f21,plain,(
% 2.39/1.06    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.39/1.06    inference(rectify,[],[f20])).
% 2.39/1.06  
% 2.39/1.06  fof(f22,plain,(
% 2.39/1.06    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.39/1.06    introduced(choice_axiom,[])).
% 2.39/1.06  
% 2.39/1.06  fof(f23,plain,(
% 2.39/1.06    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.39/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 2.39/1.06  
% 2.39/1.06  fof(f38,plain,(
% 2.39/1.06    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.39/1.06    inference(cnf_transformation,[],[f23])).
% 2.39/1.06  
% 2.39/1.06  fof(f48,plain,(
% 2.39/1.06    l1_pre_topc(sK2)),
% 2.39/1.06    inference(cnf_transformation,[],[f32])).
% 2.39/1.06  
% 2.39/1.06  fof(f52,plain,(
% 2.39/1.06    v1_funct_1(sK4)),
% 2.39/1.06    inference(cnf_transformation,[],[f32])).
% 2.39/1.06  
% 2.39/1.06  fof(f53,plain,(
% 2.39/1.06    v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))),
% 2.39/1.06    inference(cnf_transformation,[],[f32])).
% 2.39/1.06  
% 2.39/1.06  fof(f5,axiom,(
% 2.39/1.06    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.39/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/1.06  
% 2.39/1.06  fof(f15,plain,(
% 2.39/1.06    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.39/1.06    inference(ennf_transformation,[],[f5])).
% 2.39/1.06  
% 2.39/1.06  fof(f40,plain,(
% 2.39/1.06    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.39/1.06    inference(cnf_transformation,[],[f15])).
% 2.39/1.06  
% 2.39/1.06  fof(f57,plain,(
% 2.39/1.06    ~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v5_pre_topc(sK3,sK1,sK2)),
% 2.39/1.06    inference(cnf_transformation,[],[f32])).
% 2.39/1.06  
% 2.39/1.06  fof(f55,plain,(
% 2.39/1.06    sK3 = sK4),
% 2.39/1.06    inference(cnf_transformation,[],[f32])).
% 2.39/1.06  
% 2.39/1.06  fof(f4,axiom,(
% 2.39/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.39/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/1.06  
% 2.39/1.06  fof(f9,plain,(
% 2.39/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 2.39/1.06    inference(pure_predicate_removal,[],[f4])).
% 2.39/1.06  
% 2.39/1.06  fof(f14,plain,(
% 2.39/1.06    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.39/1.06    inference(ennf_transformation,[],[f9])).
% 2.39/1.06  
% 2.39/1.06  fof(f39,plain,(
% 2.39/1.06    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.39/1.06    inference(cnf_transformation,[],[f14])).
% 2.39/1.06  
% 2.39/1.06  fof(f51,plain,(
% 2.39/1.06    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 2.39/1.06    inference(cnf_transformation,[],[f32])).
% 2.39/1.06  
% 2.39/1.06  fof(f37,plain,(
% 2.39/1.06    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v4_pre_topc(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.39/1.06    inference(cnf_transformation,[],[f23])).
% 2.39/1.06  
% 2.39/1.06  fof(f50,plain,(
% 2.39/1.06    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 2.39/1.06    inference(cnf_transformation,[],[f32])).
% 2.39/1.06  
% 2.39/1.06  fof(f36,plain,(
% 2.39/1.06    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.39/1.06    inference(cnf_transformation,[],[f23])).
% 2.39/1.06  
% 2.39/1.06  fof(f35,plain,(
% 2.39/1.06    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.39/1.06    inference(cnf_transformation,[],[f23])).
% 2.39/1.06  
% 2.39/1.06  fof(f56,plain,(
% 2.39/1.06    v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | v5_pre_topc(sK3,sK1,sK2)),
% 2.39/1.06    inference(cnf_transformation,[],[f32])).
% 2.39/1.06  
% 2.39/1.06  fof(f1,axiom,(
% 2.39/1.06    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 2.39/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/1.06  
% 2.39/1.06  fof(f10,plain,(
% 2.39/1.06    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.39/1.06    inference(ennf_transformation,[],[f1])).
% 2.39/1.06  
% 2.39/1.06  fof(f33,plain,(
% 2.39/1.06    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.39/1.06    inference(cnf_transformation,[],[f10])).
% 2.39/1.06  
% 2.39/1.06  fof(f43,plain,(
% 2.39/1.06    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.39/1.06    inference(cnf_transformation,[],[f25])).
% 2.39/1.06  
% 2.39/1.06  cnf(c_11,plain,
% 2.39/1.06      ( ~ v4_pre_topc(X0,X1)
% 2.39/1.06      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.39/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.39/1.06      | ~ v2_pre_topc(X1)
% 2.39/1.06      | ~ l1_pre_topc(X1) ),
% 2.39/1.06      inference(cnf_transformation,[],[f41]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_24,negated_conjecture,
% 2.39/1.06      ( v2_pre_topc(sK1) ),
% 2.39/1.06      inference(cnf_transformation,[],[f45]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_397,plain,
% 2.39/1.06      ( ~ v4_pre_topc(X0,X1)
% 2.39/1.06      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.39/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.39/1.06      | ~ l1_pre_topc(X1)
% 2.39/1.06      | sK1 != X1 ),
% 2.39/1.06      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_398,plain,
% 2.39/1.06      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.39/1.06      | ~ v4_pre_topc(X0,sK1)
% 2.39/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/1.06      | ~ l1_pre_topc(sK1) ),
% 2.39/1.06      inference(unflattening,[status(thm)],[c_397]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_23,negated_conjecture,
% 2.39/1.06      ( l1_pre_topc(sK1) ),
% 2.39/1.06      inference(cnf_transformation,[],[f46]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_402,plain,
% 2.39/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/1.06      | ~ v4_pre_topc(X0,sK1)
% 2.39/1.06      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 2.39/1.06      inference(global_propositional_subsumption,
% 2.39/1.06                [status(thm)],
% 2.39/1.06                [c_398,c_23]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_403,plain,
% 2.39/1.06      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.39/1.06      | ~ v4_pre_topc(X0,sK1)
% 2.39/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.39/1.06      inference(renaming,[status(thm)],[c_402]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1108,plain,
% 2.39/1.06      ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.39/1.06      | ~ v4_pre_topc(X0_47,sK1)
% 2.39/1.06      | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_403]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1839,plain,
% 2.39/1.06      ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.39/1.06      | v4_pre_topc(X0_47,sK1) != iProver_top
% 2.39/1.06      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_1108]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_15,negated_conjecture,
% 2.39/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) ),
% 2.39/1.06      inference(cnf_transformation,[],[f54]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1120,negated_conjecture,
% 2.39/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_15]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1827,plain,
% 2.39/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) = iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_1120]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1,plain,
% 2.39/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.39/1.06      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.39/1.06      inference(cnf_transformation,[],[f34]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1130,plain,
% 2.39/1.06      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.39/1.06      | k8_relset_1(X0_49,X1_49,X0_47,X1_47) = k10_relat_1(X0_47,X1_47) ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_1]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1818,plain,
% 2.39/1.06      ( k8_relset_1(X0_49,X1_49,X0_47,X1_47) = k10_relat_1(X0_47,X1_47)
% 2.39/1.06      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_1130]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2321,plain,
% 2.39/1.06      ( k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2),sK4,X0_47) = k10_relat_1(sK4,X0_47) ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_1827,c_1818]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2,plain,
% 2.39/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.39/1.06      | v5_pre_topc(X0,X1,X2)
% 2.39/1.06      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 2.39/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.39/1.06      | ~ l1_pre_topc(X2)
% 2.39/1.06      | ~ l1_pre_topc(X1)
% 2.39/1.06      | ~ v1_funct_1(X0) ),
% 2.39/1.06      inference(cnf_transformation,[],[f38]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1129,plain,
% 2.39/1.06      ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 2.39/1.06      | v5_pre_topc(X0_47,X0_48,X1_48)
% 2.39/1.06      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,sK0(X0_48,X1_48,X0_47)),X0_48)
% 2.39/1.06      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 2.39/1.06      | ~ l1_pre_topc(X0_48)
% 2.39/1.06      | ~ l1_pre_topc(X1_48)
% 2.39/1.06      | ~ v1_funct_1(X0_47) ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_2]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1819,plain,
% 2.39/1.06      ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 2.39/1.06      | v5_pre_topc(X0_47,X0_48,X1_48) = iProver_top
% 2.39/1.06      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,sK0(X0_48,X1_48,X0_47)),X0_48) != iProver_top
% 2.39/1.06      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 2.39/1.06      | l1_pre_topc(X1_48) != iProver_top
% 2.39/1.06      | l1_pre_topc(X0_48) != iProver_top
% 2.39/1.06      | v1_funct_1(X0_47) != iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_1129]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2572,plain,
% 2.39/1.06      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.39/1.06      | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.39/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
% 2.39/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.39/1.06      | l1_pre_topc(sK2) != iProver_top
% 2.39/1.06      | v1_funct_1(sK4) != iProver_top ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_2321,c_1819]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_26,plain,
% 2.39/1.06      ( l1_pre_topc(sK1) = iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_21,negated_conjecture,
% 2.39/1.06      ( l1_pre_topc(sK2) ),
% 2.39/1.06      inference(cnf_transformation,[],[f48]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_28,plain,
% 2.39/1.06      ( l1_pre_topc(sK2) = iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_17,negated_conjecture,
% 2.39/1.06      ( v1_funct_1(sK4) ),
% 2.39/1.06      inference(cnf_transformation,[],[f52]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_32,plain,
% 2.39/1.06      ( v1_funct_1(sK4) = iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_16,negated_conjecture,
% 2.39/1.06      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) ),
% 2.39/1.06      inference(cnf_transformation,[],[f53]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_33,plain,
% 2.39/1.06      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) = iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_34,plain,
% 2.39/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) = iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_7,plain,
% 2.39/1.06      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.39/1.06      | ~ l1_pre_topc(X0) ),
% 2.39/1.06      inference(cnf_transformation,[],[f40]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_49,plain,
% 2.39/1.06      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.39/1.06      | l1_pre_topc(X0) != iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_51,plain,
% 2.39/1.06      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 2.39/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 2.39/1.06      inference(instantiation,[status(thm)],[c_49]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_12,negated_conjecture,
% 2.39/1.06      ( ~ v5_pre_topc(sK3,sK1,sK2)
% 2.39/1.06      | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
% 2.39/1.06      inference(cnf_transformation,[],[f57]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1123,negated_conjecture,
% 2.39/1.06      ( ~ v5_pre_topc(sK3,sK1,sK2)
% 2.39/1.06      | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_12]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1825,plain,
% 2.39/1.06      ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_1123]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_14,negated_conjecture,
% 2.39/1.06      ( sK3 = sK4 ),
% 2.39/1.06      inference(cnf_transformation,[],[f55]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1121,negated_conjecture,
% 2.39/1.06      ( sK3 = sK4 ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_14]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1879,plain,
% 2.39/1.06      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
% 2.39/1.06      inference(light_normalisation,[status(thm)],[c_1825,c_1121]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_6,plain,
% 2.39/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.39/1.06      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 2.39/1.06      inference(cnf_transformation,[],[f39]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1125,plain,
% 2.39/1.06      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k1_zfmisc_1(X0_49)))
% 2.39/1.06      | l1_pre_topc(g1_pre_topc(X0_49,X0_47)) ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_6]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2060,plain,
% 2.39/1.06      ( ~ m1_subset_1(u1_pre_topc(X0_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_48))))
% 2.39/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_48),u1_pre_topc(X0_48))) ),
% 2.39/1.06      inference(instantiation,[status(thm)],[c_1125]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2061,plain,
% 2.39/1.06      ( m1_subset_1(u1_pre_topc(X0_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_48)))) != iProver_top
% 2.39/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_48),u1_pre_topc(X0_48))) = iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_2060]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2063,plain,
% 2.39/1.06      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 2.39/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 2.39/1.06      inference(instantiation,[status(thm)],[c_2061]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_18,negated_conjecture,
% 2.39/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.39/1.06      inference(cnf_transformation,[],[f51]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1117,negated_conjecture,
% 2.39/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_18]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1830,plain,
% 2.39/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_1117]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1855,plain,
% 2.39/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 2.39/1.06      inference(light_normalisation,[status(thm)],[c_1830,c_1121]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3,plain,
% 2.39/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.39/1.06      | v5_pre_topc(X0,X1,X2)
% 2.39/1.06      | v4_pre_topc(sK0(X1,X2,X0),X2)
% 2.39/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.39/1.06      | ~ l1_pre_topc(X2)
% 2.39/1.06      | ~ l1_pre_topc(X1)
% 2.39/1.06      | ~ v1_funct_1(X0) ),
% 2.39/1.06      inference(cnf_transformation,[],[f37]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1128,plain,
% 2.39/1.06      ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 2.39/1.06      | v5_pre_topc(X0_47,X0_48,X1_48)
% 2.39/1.06      | v4_pre_topc(sK0(X0_48,X1_48,X0_47),X1_48)
% 2.39/1.06      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 2.39/1.06      | ~ l1_pre_topc(X0_48)
% 2.39/1.06      | ~ l1_pre_topc(X1_48)
% 2.39/1.06      | ~ v1_funct_1(X0_47) ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_3]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1820,plain,
% 2.39/1.06      ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 2.39/1.06      | v5_pre_topc(X0_47,X0_48,X1_48) = iProver_top
% 2.39/1.06      | v4_pre_topc(sK0(X0_48,X1_48,X0_47),X1_48) = iProver_top
% 2.39/1.06      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 2.39/1.06      | l1_pre_topc(X1_48) != iProver_top
% 2.39/1.06      | l1_pre_topc(X0_48) != iProver_top
% 2.39/1.06      | v1_funct_1(X0_47) != iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_1128]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2652,plain,
% 2.39/1.06      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.39/1.06      | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
% 2.39/1.06      | l1_pre_topc(sK2) != iProver_top
% 2.39/1.06      | l1_pre_topc(sK1) != iProver_top
% 2.39/1.06      | v1_funct_1(sK4) != iProver_top ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_1855,c_1820]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_19,negated_conjecture,
% 2.39/1.06      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.39/1.06      inference(cnf_transformation,[],[f50]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1116,negated_conjecture,
% 2.39/1.06      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_19]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1831,plain,
% 2.39/1.06      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_1116]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1852,plain,
% 2.39/1.06      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 2.39/1.06      inference(light_normalisation,[status(thm)],[c_1831,c_1121]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3141,plain,
% 2.39/1.06      ( v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 2.39/1.06      inference(global_propositional_subsumption,
% 2.39/1.06                [status(thm)],
% 2.39/1.06                [c_2652,c_26,c_28,c_32,c_1852]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3142,plain,
% 2.39/1.06      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.39/1.06      | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top ),
% 2.39/1.06      inference(renaming,[status(thm)],[c_3141]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2323,plain,
% 2.39/1.06      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0_47) = k10_relat_1(sK4,X0_47) ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_1855,c_1818]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2573,plain,
% 2.39/1.06      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.39/1.06      | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top
% 2.39/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.39/1.06      | l1_pre_topc(sK2) != iProver_top
% 2.39/1.06      | l1_pre_topc(sK1) != iProver_top
% 2.39/1.06      | v1_funct_1(sK4) != iProver_top ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_2323,c_1819]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3679,plain,
% 2.39/1.06      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.39/1.06      | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top ),
% 2.39/1.06      inference(global_propositional_subsumption,
% 2.39/1.06                [status(thm)],
% 2.39/1.06                [c_2573,c_26,c_28,c_32,c_1852,c_1855]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_4,plain,
% 2.39/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.39/1.06      | v5_pre_topc(X0,X1,X2)
% 2.39/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.39/1.06      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 2.39/1.06      | ~ l1_pre_topc(X2)
% 2.39/1.06      | ~ l1_pre_topc(X1)
% 2.39/1.06      | ~ v1_funct_1(X0) ),
% 2.39/1.06      inference(cnf_transformation,[],[f36]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1127,plain,
% 2.39/1.06      ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 2.39/1.06      | v5_pre_topc(X0_47,X0_48,X1_48)
% 2.39/1.06      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 2.39/1.06      | m1_subset_1(sK0(X0_48,X1_48,X0_47),k1_zfmisc_1(u1_struct_0(X1_48)))
% 2.39/1.06      | ~ l1_pre_topc(X0_48)
% 2.39/1.06      | ~ l1_pre_topc(X1_48)
% 2.39/1.06      | ~ v1_funct_1(X0_47) ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_4]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1821,plain,
% 2.39/1.06      ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 2.39/1.06      | v5_pre_topc(X0_47,X0_48,X1_48) = iProver_top
% 2.39/1.06      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 2.39/1.06      | m1_subset_1(sK0(X0_48,X1_48,X0_47),k1_zfmisc_1(u1_struct_0(X1_48))) = iProver_top
% 2.39/1.06      | l1_pre_topc(X1_48) != iProver_top
% 2.39/1.06      | l1_pre_topc(X0_48) != iProver_top
% 2.39/1.06      | v1_funct_1(X0_47) != iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_1127]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2743,plain,
% 2.39/1.06      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.39/1.06      | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.39/1.06      | l1_pre_topc(sK2) != iProver_top
% 2.39/1.06      | l1_pre_topc(sK1) != iProver_top
% 2.39/1.06      | v1_funct_1(sK4) != iProver_top ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_1855,c_1821]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3186,plain,
% 2.39/1.06      ( m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 2.39/1.06      inference(global_propositional_subsumption,
% 2.39/1.06                [status(thm)],
% 2.39/1.06                [c_2743,c_26,c_28,c_32,c_1852]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3187,plain,
% 2.39/1.06      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.39/1.06      | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.39/1.06      inference(renaming,[status(thm)],[c_3186]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_5,plain,
% 2.39/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.39/1.06      | ~ v5_pre_topc(X0,X1,X2)
% 2.39/1.06      | ~ v4_pre_topc(X3,X2)
% 2.39/1.06      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 2.39/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.39/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.39/1.06      | ~ l1_pre_topc(X2)
% 2.39/1.06      | ~ l1_pre_topc(X1)
% 2.39/1.06      | ~ v1_funct_1(X0) ),
% 2.39/1.06      inference(cnf_transformation,[],[f35]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1126,plain,
% 2.39/1.06      ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 2.39/1.06      | ~ v5_pre_topc(X0_47,X0_48,X1_48)
% 2.39/1.06      | ~ v4_pre_topc(X1_47,X1_48)
% 2.39/1.06      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,X1_47),X0_48)
% 2.39/1.06      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 2.39/1.06      | ~ m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(X1_48)))
% 2.39/1.06      | ~ l1_pre_topc(X0_48)
% 2.39/1.06      | ~ l1_pre_topc(X1_48)
% 2.39/1.06      | ~ v1_funct_1(X0_47) ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_5]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1822,plain,
% 2.39/1.06      ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 2.39/1.06      | v5_pre_topc(X0_47,X0_48,X1_48) != iProver_top
% 2.39/1.06      | v4_pre_topc(X1_47,X1_48) != iProver_top
% 2.39/1.06      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,X1_47),X0_48) = iProver_top
% 2.39/1.06      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 2.39/1.06      | m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(X1_48))) != iProver_top
% 2.39/1.06      | l1_pre_topc(X1_48) != iProver_top
% 2.39/1.06      | l1_pre_topc(X0_48) != iProver_top
% 2.39/1.06      | v1_funct_1(X0_47) != iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_1126]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2798,plain,
% 2.39/1.06      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,sK1,sK2) != iProver_top
% 2.39/1.06      | v4_pre_topc(X0_47,sK2) != iProver_top
% 2.39/1.06      | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top
% 2.39/1.06      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.39/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.39/1.06      | l1_pre_topc(sK2) != iProver_top
% 2.39/1.06      | l1_pre_topc(sK1) != iProver_top
% 2.39/1.06      | v1_funct_1(sK4) != iProver_top ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_2323,c_1822]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_13,negated_conjecture,
% 2.39/1.06      ( v5_pre_topc(sK3,sK1,sK2)
% 2.39/1.06      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
% 2.39/1.06      inference(cnf_transformation,[],[f56]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1122,negated_conjecture,
% 2.39/1.06      ( v5_pre_topc(sK3,sK1,sK2)
% 2.39/1.06      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_13]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1826,plain,
% 2.39/1.06      ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_1122]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1870,plain,
% 2.39/1.06      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 2.39/1.06      inference(light_normalisation,[status(thm)],[c_1826,c_1121]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2797,plain,
% 2.39/1.06      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 2.39/1.06      | v4_pre_topc(X0_47,sK2) != iProver_top
% 2.39/1.06      | v4_pre_topc(k10_relat_1(sK4,X0_47),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.39/1.06      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.39/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
% 2.39/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.39/1.06      | l1_pre_topc(sK2) != iProver_top
% 2.39/1.06      | v1_funct_1(sK4) != iProver_top ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_2321,c_1822]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_0,plain,
% 2.39/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.39/1.06      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 2.39/1.06      inference(cnf_transformation,[],[f33]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1131,plain,
% 2.39/1.06      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.39/1.06      | m1_subset_1(k8_relset_1(X0_49,X1_49,X0_47,X1_47),k1_zfmisc_1(X0_49)) ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_0]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1817,plain,
% 2.39/1.06      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 2.39/1.06      | m1_subset_1(k8_relset_1(X0_49,X1_49,X0_47,X1_47),k1_zfmisc_1(X0_49)) = iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_1131]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2383,plain,
% 2.39/1.06      ( m1_subset_1(k10_relat_1(sK4,X0_47),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
% 2.39/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_2321,c_1817]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3300,plain,
% 2.39/1.06      ( m1_subset_1(k10_relat_1(sK4,X0_47),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
% 2.39/1.06      inference(global_propositional_subsumption,
% 2.39/1.06                [status(thm)],
% 2.39/1.06                [c_2383,c_34]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_9,plain,
% 2.39/1.06      ( v4_pre_topc(X0,X1)
% 2.39/1.06      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.39/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 2.39/1.06      | ~ v2_pre_topc(X1)
% 2.39/1.06      | ~ l1_pre_topc(X1) ),
% 2.39/1.06      inference(cnf_transformation,[],[f43]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_439,plain,
% 2.39/1.06      ( v4_pre_topc(X0,X1)
% 2.39/1.06      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.39/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 2.39/1.06      | ~ l1_pre_topc(X1)
% 2.39/1.06      | sK1 != X1 ),
% 2.39/1.06      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_440,plain,
% 2.39/1.06      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.39/1.06      | v4_pre_topc(X0,sK1)
% 2.39/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 2.39/1.06      | ~ l1_pre_topc(sK1) ),
% 2.39/1.06      inference(unflattening,[status(thm)],[c_439]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_444,plain,
% 2.39/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 2.39/1.06      | v4_pre_topc(X0,sK1)
% 2.39/1.06      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 2.39/1.06      inference(global_propositional_subsumption,
% 2.39/1.06                [status(thm)],
% 2.39/1.06                [c_440,c_23]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_445,plain,
% 2.39/1.06      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.39/1.06      | v4_pre_topc(X0,sK1)
% 2.39/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
% 2.39/1.06      inference(renaming,[status(thm)],[c_444]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1106,plain,
% 2.39/1.06      ( ~ v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.39/1.06      | v4_pre_topc(X0_47,sK1)
% 2.39/1.06      | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
% 2.39/1.06      inference(subtyping,[status(esa)],[c_445]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_1841,plain,
% 2.39/1.06      ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.39/1.06      | v4_pre_topc(X0_47,sK1) = iProver_top
% 2.39/1.06      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
% 2.39/1.06      inference(predicate_to_equality,[status(thm)],[c_1106]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3308,plain,
% 2.39/1.06      ( v4_pre_topc(k10_relat_1(sK4,X0_47),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.39/1.06      | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_3300,c_1841]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3686,plain,
% 2.39/1.06      ( v4_pre_topc(X0_47,sK2) != iProver_top
% 2.39/1.06      | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top
% 2.39/1.06      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.39/1.06      inference(global_propositional_subsumption,
% 2.39/1.06                [status(thm)],
% 2.39/1.06                [c_2798,c_26,c_28,c_32,c_33,c_34,c_51,c_1870,c_1852,
% 2.39/1.06                 c_1855,c_2063,c_2797,c_3308]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3697,plain,
% 2.39/1.06      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.39/1.06      | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) != iProver_top
% 2.39/1.06      | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) = iProver_top ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_3187,c_3686]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3792,plain,
% 2.39/1.06      ( v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 2.39/1.06      inference(global_propositional_subsumption,
% 2.39/1.06                [status(thm)],
% 2.39/1.06                [c_2572,c_26,c_28,c_32,c_33,c_34,c_51,c_1879,c_2063,
% 2.39/1.06                 c_3142,c_3679,c_3697]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3797,plain,
% 2.39/1.06      ( v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),sK1) != iProver_top
% 2.39/1.06      | m1_subset_1(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_1839,c_3792]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2378,plain,
% 2.39/1.06      ( m1_subset_1(k10_relat_1(sK4,X0_47),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.39/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_2323,c_1817]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3292,plain,
% 2.39/1.06      ( m1_subset_1(k10_relat_1(sK4,X0_47),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.39/1.06      inference(global_propositional_subsumption,
% 2.39/1.06                [status(thm)],
% 2.39/1.06                [c_2378,c_1855]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_4032,plain,
% 2.39/1.06      ( v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),sK1) != iProver_top ),
% 2.39/1.06      inference(forward_subsumption_resolution,
% 2.39/1.06                [status(thm)],
% 2.39/1.06                [c_3797,c_3292]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2741,plain,
% 2.39/1.06      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.39/1.06      | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.39/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.39/1.06      | l1_pre_topc(sK2) != iProver_top
% 2.39/1.06      | v1_funct_1(sK4) != iProver_top ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_1827,c_1821]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3235,plain,
% 2.39/1.06      ( m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
% 2.39/1.06      inference(global_propositional_subsumption,
% 2.39/1.06                [status(thm)],
% 2.39/1.06                [c_2741,c_26,c_28,c_32,c_33,c_51,c_2063]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3236,plain,
% 2.39/1.06      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.39/1.06      | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.39/1.06      inference(renaming,[status(thm)],[c_3235]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3696,plain,
% 2.39/1.06      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.39/1.06      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) != iProver_top
% 2.39/1.06      | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),sK1) = iProver_top ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_3236,c_3686]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_2650,plain,
% 2.39/1.06      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.39/1.06      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top
% 2.39/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.39/1.06      | l1_pre_topc(sK2) != iProver_top
% 2.39/1.06      | v1_funct_1(sK4) != iProver_top ),
% 2.39/1.06      inference(superposition,[status(thm)],[c_1827,c_1820]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3193,plain,
% 2.39/1.06      ( v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top
% 2.39/1.06      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
% 2.39/1.06      inference(global_propositional_subsumption,
% 2.39/1.06                [status(thm)],
% 2.39/1.06                [c_2650,c_26,c_28,c_32,c_33,c_51,c_2063]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(c_3194,plain,
% 2.39/1.06      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.39/1.06      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top ),
% 2.39/1.06      inference(renaming,[status(thm)],[c_3193]) ).
% 2.39/1.06  
% 2.39/1.06  cnf(contradiction,plain,
% 2.39/1.06      ( $false ),
% 2.39/1.06      inference(minisat,
% 2.39/1.06                [status(thm)],
% 2.39/1.06                [c_4032,c_3697,c_3696,c_3679,c_3194,c_3142,c_1879]) ).
% 2.39/1.06  
% 2.39/1.06  
% 2.39/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 2.39/1.06  
% 2.39/1.06  ------                               Statistics
% 2.39/1.06  
% 2.39/1.06  ------ General
% 2.39/1.06  
% 2.39/1.06  abstr_ref_over_cycles:                  0
% 2.39/1.06  abstr_ref_under_cycles:                 0
% 2.39/1.06  gc_basic_clause_elim:                   0
% 2.39/1.06  forced_gc_time:                         0
% 2.39/1.06  parsing_time:                           0.011
% 2.39/1.06  unif_index_cands_time:                  0.
% 2.39/1.06  unif_index_add_time:                    0.
% 2.39/1.06  orderings_time:                         0.
% 2.39/1.06  out_proof_time:                         0.011
% 2.39/1.06  total_time:                             0.187
% 2.39/1.06  num_of_symbols:                         56
% 2.39/1.06  num_of_terms:                           3588
% 2.39/1.06  
% 2.39/1.06  ------ Preprocessing
% 2.39/1.06  
% 2.39/1.06  num_of_splits:                          0
% 2.39/1.06  num_of_split_atoms:                     0
% 2.39/1.06  num_of_reused_defs:                     0
% 2.39/1.06  num_eq_ax_congr_red:                    12
% 2.39/1.06  num_of_sem_filtered_clauses:            1
% 2.39/1.06  num_of_subtypes:                        3
% 2.39/1.06  monotx_restored_types:                  0
% 2.39/1.06  sat_num_of_epr_types:                   0
% 2.39/1.06  sat_num_of_non_cyclic_types:            0
% 2.39/1.06  sat_guarded_non_collapsed_types:        0
% 2.39/1.06  num_pure_diseq_elim:                    0
% 2.39/1.06  simp_replaced_by:                       0
% 2.39/1.06  res_preprocessed:                       112
% 2.39/1.06  prep_upred:                             0
% 2.39/1.06  prep_unflattend:                        24
% 2.39/1.06  smt_new_axioms:                         0
% 2.39/1.06  pred_elim_cands:                        7
% 2.39/1.06  pred_elim:                              1
% 2.39/1.06  pred_elim_cl:                           -2
% 2.39/1.06  pred_elim_cycles:                       3
% 2.39/1.06  merged_defs:                            6
% 2.39/1.06  merged_defs_ncl:                        0
% 2.39/1.06  bin_hyper_res:                          6
% 2.39/1.06  prep_cycles:                            3
% 2.39/1.06  pred_elim_time:                         0.022
% 2.39/1.06  splitting_time:                         0.
% 2.39/1.06  sem_filter_time:                        0.
% 2.39/1.06  monotx_time:                            0.
% 2.39/1.06  subtype_inf_time:                       0.001
% 2.39/1.06  
% 2.39/1.06  ------ Problem properties
% 2.39/1.06  
% 2.39/1.06  clauses:                                27
% 2.39/1.06  conjectures:                            11
% 2.39/1.06  epr:                                    5
% 2.39/1.06  horn:                                   24
% 2.39/1.06  ground:                                 11
% 2.39/1.06  unary:                                  9
% 2.39/1.06  binary:                                 6
% 2.39/1.06  lits:                                   75
% 2.39/1.06  lits_eq:                                2
% 2.39/1.06  fd_pure:                                0
% 2.39/1.06  fd_pseudo:                              0
% 2.39/1.06  fd_cond:                                0
% 2.39/1.06  fd_pseudo_cond:                         0
% 2.39/1.06  ac_symbols:                             0
% 2.39/1.06  
% 2.39/1.06  ------ Propositional Solver
% 2.39/1.06  
% 2.39/1.06  prop_solver_calls:                      22
% 2.39/1.06  prop_fast_solver_calls:                 1095
% 2.39/1.06  smt_solver_calls:                       0
% 2.39/1.06  smt_fast_solver_calls:                  0
% 2.39/1.06  prop_num_of_clauses:                    1224
% 2.39/1.06  prop_preprocess_simplified:             4215
% 2.39/1.06  prop_fo_subsumed:                       61
% 2.39/1.06  prop_solver_time:                       0.
% 2.39/1.06  smt_solver_time:                        0.
% 2.39/1.06  smt_fast_solver_time:                   0.
% 2.39/1.06  prop_fast_solver_time:                  0.
% 2.39/1.06  prop_unsat_core_time:                   0.
% 2.39/1.06  
% 2.39/1.06  ------ QBF
% 2.39/1.06  
% 2.39/1.06  qbf_q_res:                              0
% 2.39/1.06  qbf_num_tautologies:                    0
% 2.39/1.06  qbf_prep_cycles:                        0
% 2.39/1.06  
% 2.39/1.06  ------ BMC1
% 2.39/1.06  
% 2.39/1.06  bmc1_current_bound:                     -1
% 2.39/1.06  bmc1_last_solved_bound:                 -1
% 2.39/1.06  bmc1_unsat_core_size:                   -1
% 2.39/1.06  bmc1_unsat_core_parents_size:           -1
% 2.39/1.06  bmc1_merge_next_fun:                    0
% 2.39/1.06  bmc1_unsat_core_clauses_time:           0.
% 2.39/1.06  
% 2.39/1.06  ------ Instantiation
% 2.39/1.06  
% 2.39/1.06  inst_num_of_clauses:                    329
% 2.39/1.06  inst_num_in_passive:                    76
% 2.39/1.06  inst_num_in_active:                     242
% 2.39/1.06  inst_num_in_unprocessed:                11
% 2.39/1.06  inst_num_of_loops:                      270
% 2.39/1.06  inst_num_of_learning_restarts:          0
% 2.39/1.06  inst_num_moves_active_passive:          24
% 2.39/1.06  inst_lit_activity:                      0
% 2.39/1.06  inst_lit_activity_moves:                0
% 2.39/1.06  inst_num_tautologies:                   0
% 2.39/1.06  inst_num_prop_implied:                  0
% 2.39/1.06  inst_num_existing_simplified:           0
% 2.39/1.06  inst_num_eq_res_simplified:             0
% 2.39/1.06  inst_num_child_elim:                    0
% 2.39/1.06  inst_num_of_dismatching_blockings:      34
% 2.39/1.06  inst_num_of_non_proper_insts:           266
% 2.39/1.06  inst_num_of_duplicates:                 0
% 2.39/1.06  inst_inst_num_from_inst_to_res:         0
% 2.39/1.06  inst_dismatching_checking_time:         0.
% 2.39/1.06  
% 2.39/1.06  ------ Resolution
% 2.39/1.06  
% 2.39/1.06  res_num_of_clauses:                     0
% 2.39/1.06  res_num_in_passive:                     0
% 2.39/1.06  res_num_in_active:                      0
% 2.39/1.06  res_num_of_loops:                       115
% 2.39/1.06  res_forward_subset_subsumed:            25
% 2.39/1.06  res_backward_subset_subsumed:           0
% 2.39/1.06  res_forward_subsumed:                   0
% 2.39/1.06  res_backward_subsumed:                  0
% 2.39/1.06  res_forward_subsumption_resolution:     0
% 2.39/1.06  res_backward_subsumption_resolution:    0
% 2.39/1.06  res_clause_to_clause_subsumption:       120
% 2.39/1.06  res_orphan_elimination:                 0
% 2.39/1.06  res_tautology_del:                      57
% 2.39/1.06  res_num_eq_res_simplified:              0
% 2.39/1.06  res_num_sel_changes:                    0
% 2.39/1.06  res_moves_from_active_to_pass:          0
% 2.39/1.06  
% 2.39/1.06  ------ Superposition
% 2.39/1.06  
% 2.39/1.06  sup_time_total:                         0.
% 2.39/1.06  sup_time_generating:                    0.
% 2.39/1.06  sup_time_sim_full:                      0.
% 2.39/1.06  sup_time_sim_immed:                     0.
% 2.39/1.06  
% 2.39/1.06  sup_num_of_clauses:                     64
% 2.39/1.06  sup_num_in_active:                      53
% 2.39/1.06  sup_num_in_passive:                     11
% 2.39/1.06  sup_num_of_loops:                       53
% 2.39/1.06  sup_fw_superposition:                   44
% 2.39/1.06  sup_bw_superposition:                   8
% 2.39/1.06  sup_immediate_simplified:               5
% 2.39/1.06  sup_given_eliminated:                   0
% 2.39/1.06  comparisons_done:                       0
% 2.39/1.06  comparisons_avoided:                    0
% 2.39/1.06  
% 2.39/1.06  ------ Simplifications
% 2.39/1.06  
% 2.39/1.06  
% 2.39/1.06  sim_fw_subset_subsumed:                 2
% 2.39/1.06  sim_bw_subset_subsumed:                 0
% 2.39/1.06  sim_fw_subsumed:                        2
% 2.39/1.06  sim_bw_subsumed:                        0
% 2.39/1.06  sim_fw_subsumption_res:                 1
% 2.39/1.06  sim_bw_subsumption_res:                 0
% 2.39/1.06  sim_tautology_del:                      11
% 2.39/1.06  sim_eq_tautology_del:                   0
% 2.39/1.06  sim_eq_res_simp:                        0
% 2.39/1.06  sim_fw_demodulated:                     1
% 2.39/1.06  sim_bw_demodulated:                     0
% 2.39/1.06  sim_light_normalised:                   7
% 2.39/1.06  sim_joinable_taut:                      0
% 2.39/1.06  sim_joinable_simp:                      0
% 2.39/1.06  sim_ac_normalised:                      0
% 2.39/1.06  sim_smt_subsumption:                    0
% 2.39/1.06  
%------------------------------------------------------------------------------
