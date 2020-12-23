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
% DateTime   : Thu Dec  3 12:11:55 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  198 (1877 expanded)
%              Number of clauses        :  114 ( 563 expanded)
%              Number of leaves         :   17 ( 430 expanded)
%              Depth                    :   22
%              Number of atoms          : 1039 (15675 expanded)
%              Number of equality atoms :  293 (1811 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f56,plain,(
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
     => ( ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK7 = X2
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
              | ~ v5_pre_topc(sK6,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK6,X0,X1) )
            & sK6 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
                  | ~ v5_pre_topc(X2,X0,sK5) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
                  | v5_pre_topc(X2,X0,sK5) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK5))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK5)
        & v2_pre_topc(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK4,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK4,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
      | ~ v5_pre_topc(sK6,sK4,sK5) )
    & ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
      | v5_pre_topc(sK6,sK4,sK5) )
    & sK6 = sK7
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    & v1_funct_1(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f52,f56,f55,f54,f53])).

fof(f91,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f79,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(rectify,[],[f3])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f17,f31])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
            & r1_tarski(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f90,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f103,plain,(
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
    inference(equality_resolution,[],[f85])).

fof(f99,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f98,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,(
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
    inference(equality_resolution,[],[f87])).

fof(f88,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f104,plain,(
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
    inference(equality_resolution,[],[f84])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f106,plain,(
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
    inference(equality_resolution,[],[f86])).

fof(f100,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3669,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3705,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3704,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_22,plain,
    ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3685,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7528,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | r1_tarski(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3704,c_3685])).

cnf(c_8211,plain,
    ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3705,c_7528])).

cnf(c_21,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_79,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3687,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3688,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4810,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3687,c_3688])).

cnf(c_17,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4119,plain,
    ( v3_pre_topc(u1_struct_0(X0),X0)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_5237,plain,
    ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
    | ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_4119])).

cnf(c_5240,plain,
    ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5237])).

cnf(c_5239,plain,
    ( ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_5244,plain,
    ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5239])).

cnf(c_16,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6336,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6337,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6336])).

cnf(c_4319,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7010,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
    | ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ),
    inference(instantiation,[status(thm)],[c_4319])).

cnf(c_7011,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) = iProver_top
    | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7010])).

cnf(c_4620,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_8131,plain,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ),
    inference(instantiation,[status(thm)],[c_4620])).

cnf(c_8132,plain,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8131])).

cnf(c_8227,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8211,c_79,c_4810,c_5240,c_5244,c_6337,c_7011,c_8132])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3703,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8236,plain,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8227,c_3703])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3706,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8410,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8236,c_3706])).

cnf(c_4320,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4319])).

cnf(c_4621,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4620])).

cnf(c_24,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_5220,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X0)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_5229,plain,
    ( v3_pre_topc(u1_struct_0(X0),X0) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5220])).

cnf(c_6033,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7156,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
    | r1_tarski(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ),
    inference(instantiation,[status(thm)],[c_6033])).

cnf(c_7157,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7156])).

cnf(c_3691,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3690,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6130,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3704,c_3690])).

cnf(c_7341,plain,
    ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3691,c_6130])).

cnf(c_8426,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8410,c_4320,c_4621,c_5229,c_7157,c_7341])).

cnf(c_8435,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3669,c_8426])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_45,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_8612,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8435,c_45])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3675,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8627,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8612,c_3675])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3681,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9613,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
    | v5_pre_topc(sK7,sK4,sK5) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8627,c_3681])).

cnf(c_31,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK5)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3676,plain,
    ( v5_pre_topc(sK6,sK4,sK5) = iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_32,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3792,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v5_pre_topc(sK7,sK4,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3676,c_32])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3679,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5384,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3675,c_3679])).

cnf(c_42,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_43,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_44,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_46,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_50,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_51,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_81,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_82,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_84,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_4100,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4101,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4100])).

cnf(c_4103,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4101])).

cnf(c_5613,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5384,c_43,c_44,c_45,c_46,c_50,c_51,c_81,c_84,c_4103])).

cnf(c_5614,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5613])).

cnf(c_5622,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
    | v5_pre_topc(sK7,sK4,sK5) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3792,c_5614])).

cnf(c_9615,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
    | v5_pre_topc(sK7,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_8627,c_5622])).

cnf(c_9659,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(sK7,sK4,sK5) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9613,c_9615])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3680,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_9614,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
    | v5_pre_topc(sK7,sK4,sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8627,c_3680])).

cnf(c_9639,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9614,c_9615])).

cnf(c_3674,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_8628,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8612,c_3674])).

cnf(c_4451,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3675,c_3703])).

cnf(c_8626,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8612,c_4451])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3678,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4659,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3675,c_3678])).

cnf(c_5014,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4659,c_43,c_44,c_45,c_46,c_50,c_51,c_81,c_84,c_4103])).

cnf(c_5015,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5014])).

cnf(c_5022,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
    | r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3704,c_5015])).

cnf(c_30,negated_conjecture,
    ( ~ v5_pre_topc(sK6,sK4,sK5)
    | ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_3677,plain,
    ( v5_pre_topc(sK6,sK4,sK5) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3797,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v5_pre_topc(sK7,sK4,sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3677,c_32])).

cnf(c_5101,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
    | v5_pre_topc(sK7,sK4,sK5) != iProver_top
    | r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5022,c_3797])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3672,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3725,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3672,c_32])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3671,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3722,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3671,c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9659,c_9639,c_8628,c_8626,c_5101,c_3725,c_3722,c_50,c_46,c_45,c_44,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:22:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.89/1.06  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.06  
% 2.89/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.89/1.06  
% 2.89/1.06  ------  iProver source info
% 2.89/1.06  
% 2.89/1.06  git: date: 2020-06-30 10:37:57 +0100
% 2.89/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.89/1.06  git: non_committed_changes: false
% 2.89/1.06  git: last_make_outside_of_git: false
% 2.89/1.06  
% 2.89/1.06  ------ 
% 2.89/1.06  
% 2.89/1.06  ------ Input Options
% 2.89/1.06  
% 2.89/1.06  --out_options                           all
% 2.89/1.06  --tptp_safe_out                         true
% 2.89/1.06  --problem_path                          ""
% 2.89/1.06  --include_path                          ""
% 2.89/1.06  --clausifier                            res/vclausify_rel
% 2.89/1.06  --clausifier_options                    --mode clausify
% 2.89/1.06  --stdin                                 false
% 2.89/1.06  --stats_out                             all
% 2.89/1.06  
% 2.89/1.06  ------ General Options
% 2.89/1.06  
% 2.89/1.06  --fof                                   false
% 2.89/1.06  --time_out_real                         305.
% 2.89/1.06  --time_out_virtual                      -1.
% 2.89/1.06  --symbol_type_check                     false
% 2.89/1.06  --clausify_out                          false
% 2.89/1.06  --sig_cnt_out                           false
% 2.89/1.06  --trig_cnt_out                          false
% 2.89/1.06  --trig_cnt_out_tolerance                1.
% 2.89/1.06  --trig_cnt_out_sk_spl                   false
% 2.89/1.06  --abstr_cl_out                          false
% 2.89/1.06  
% 2.89/1.06  ------ Global Options
% 2.89/1.06  
% 2.89/1.06  --schedule                              default
% 2.89/1.06  --add_important_lit                     false
% 2.89/1.06  --prop_solver_per_cl                    1000
% 2.89/1.06  --min_unsat_core                        false
% 2.89/1.06  --soft_assumptions                      false
% 2.89/1.06  --soft_lemma_size                       3
% 2.89/1.06  --prop_impl_unit_size                   0
% 2.89/1.06  --prop_impl_unit                        []
% 2.89/1.06  --share_sel_clauses                     true
% 2.89/1.06  --reset_solvers                         false
% 2.89/1.06  --bc_imp_inh                            [conj_cone]
% 2.89/1.06  --conj_cone_tolerance                   3.
% 2.89/1.06  --extra_neg_conj                        none
% 2.89/1.06  --large_theory_mode                     true
% 2.89/1.06  --prolific_symb_bound                   200
% 2.89/1.06  --lt_threshold                          2000
% 2.89/1.06  --clause_weak_htbl                      true
% 2.89/1.06  --gc_record_bc_elim                     false
% 2.89/1.06  
% 2.89/1.06  ------ Preprocessing Options
% 2.89/1.06  
% 2.89/1.06  --preprocessing_flag                    true
% 2.89/1.06  --time_out_prep_mult                    0.1
% 2.89/1.06  --splitting_mode                        input
% 2.89/1.06  --splitting_grd                         true
% 2.89/1.06  --splitting_cvd                         false
% 2.89/1.06  --splitting_cvd_svl                     false
% 2.89/1.06  --splitting_nvd                         32
% 2.89/1.06  --sub_typing                            true
% 2.89/1.06  --prep_gs_sim                           true
% 2.89/1.06  --prep_unflatten                        true
% 2.89/1.06  --prep_res_sim                          true
% 2.89/1.06  --prep_upred                            true
% 2.89/1.06  --prep_sem_filter                       exhaustive
% 2.89/1.06  --prep_sem_filter_out                   false
% 2.89/1.06  --pred_elim                             true
% 2.89/1.06  --res_sim_input                         true
% 2.89/1.06  --eq_ax_congr_red                       true
% 2.89/1.06  --pure_diseq_elim                       true
% 2.89/1.06  --brand_transform                       false
% 2.89/1.06  --non_eq_to_eq                          false
% 2.89/1.06  --prep_def_merge                        true
% 2.89/1.06  --prep_def_merge_prop_impl              false
% 2.89/1.06  --prep_def_merge_mbd                    true
% 2.89/1.06  --prep_def_merge_tr_red                 false
% 2.89/1.06  --prep_def_merge_tr_cl                  false
% 2.89/1.06  --smt_preprocessing                     true
% 2.89/1.06  --smt_ac_axioms                         fast
% 2.89/1.06  --preprocessed_out                      false
% 2.89/1.06  --preprocessed_stats                    false
% 2.89/1.06  
% 2.89/1.06  ------ Abstraction refinement Options
% 2.89/1.06  
% 2.89/1.06  --abstr_ref                             []
% 2.89/1.06  --abstr_ref_prep                        false
% 2.89/1.06  --abstr_ref_until_sat                   false
% 2.89/1.06  --abstr_ref_sig_restrict                funpre
% 2.89/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/1.06  --abstr_ref_under                       []
% 2.89/1.06  
% 2.89/1.06  ------ SAT Options
% 2.89/1.06  
% 2.89/1.06  --sat_mode                              false
% 2.89/1.06  --sat_fm_restart_options                ""
% 2.89/1.06  --sat_gr_def                            false
% 2.89/1.06  --sat_epr_types                         true
% 2.89/1.06  --sat_non_cyclic_types                  false
% 2.89/1.06  --sat_finite_models                     false
% 2.89/1.06  --sat_fm_lemmas                         false
% 2.89/1.06  --sat_fm_prep                           false
% 2.89/1.06  --sat_fm_uc_incr                        true
% 2.89/1.06  --sat_out_model                         small
% 2.89/1.06  --sat_out_clauses                       false
% 2.89/1.06  
% 2.89/1.06  ------ QBF Options
% 2.89/1.06  
% 2.89/1.06  --qbf_mode                              false
% 2.89/1.06  --qbf_elim_univ                         false
% 2.89/1.06  --qbf_dom_inst                          none
% 2.89/1.06  --qbf_dom_pre_inst                      false
% 2.89/1.06  --qbf_sk_in                             false
% 2.89/1.06  --qbf_pred_elim                         true
% 2.89/1.06  --qbf_split                             512
% 2.89/1.06  
% 2.89/1.06  ------ BMC1 Options
% 2.89/1.06  
% 2.89/1.06  --bmc1_incremental                      false
% 2.89/1.06  --bmc1_axioms                           reachable_all
% 2.89/1.06  --bmc1_min_bound                        0
% 2.89/1.06  --bmc1_max_bound                        -1
% 2.89/1.06  --bmc1_max_bound_default                -1
% 2.89/1.06  --bmc1_symbol_reachability              true
% 2.89/1.06  --bmc1_property_lemmas                  false
% 2.89/1.06  --bmc1_k_induction                      false
% 2.89/1.06  --bmc1_non_equiv_states                 false
% 2.89/1.06  --bmc1_deadlock                         false
% 2.89/1.06  --bmc1_ucm                              false
% 2.89/1.06  --bmc1_add_unsat_core                   none
% 2.89/1.06  --bmc1_unsat_core_children              false
% 2.89/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/1.06  --bmc1_out_stat                         full
% 2.89/1.06  --bmc1_ground_init                      false
% 2.89/1.06  --bmc1_pre_inst_next_state              false
% 2.89/1.06  --bmc1_pre_inst_state                   false
% 2.89/1.06  --bmc1_pre_inst_reach_state             false
% 2.89/1.06  --bmc1_out_unsat_core                   false
% 2.89/1.06  --bmc1_aig_witness_out                  false
% 2.89/1.06  --bmc1_verbose                          false
% 2.89/1.06  --bmc1_dump_clauses_tptp                false
% 2.89/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.89/1.06  --bmc1_dump_file                        -
% 2.89/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.89/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.89/1.06  --bmc1_ucm_extend_mode                  1
% 2.89/1.06  --bmc1_ucm_init_mode                    2
% 2.89/1.06  --bmc1_ucm_cone_mode                    none
% 2.89/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.89/1.06  --bmc1_ucm_relax_model                  4
% 2.89/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.89/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/1.06  --bmc1_ucm_layered_model                none
% 2.89/1.06  --bmc1_ucm_max_lemma_size               10
% 2.89/1.06  
% 2.89/1.06  ------ AIG Options
% 2.89/1.06  
% 2.89/1.06  --aig_mode                              false
% 2.89/1.06  
% 2.89/1.06  ------ Instantiation Options
% 2.89/1.06  
% 2.89/1.06  --instantiation_flag                    true
% 2.89/1.06  --inst_sos_flag                         false
% 2.89/1.06  --inst_sos_phase                        true
% 2.89/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/1.06  --inst_lit_sel_side                     num_symb
% 2.89/1.06  --inst_solver_per_active                1400
% 2.89/1.06  --inst_solver_calls_frac                1.
% 2.89/1.06  --inst_passive_queue_type               priority_queues
% 2.89/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/1.06  --inst_passive_queues_freq              [25;2]
% 2.89/1.06  --inst_dismatching                      true
% 2.89/1.06  --inst_eager_unprocessed_to_passive     true
% 2.89/1.06  --inst_prop_sim_given                   true
% 2.89/1.06  --inst_prop_sim_new                     false
% 2.89/1.06  --inst_subs_new                         false
% 2.89/1.06  --inst_eq_res_simp                      false
% 2.89/1.06  --inst_subs_given                       false
% 2.89/1.06  --inst_orphan_elimination               true
% 2.89/1.06  --inst_learning_loop_flag               true
% 2.89/1.06  --inst_learning_start                   3000
% 2.89/1.06  --inst_learning_factor                  2
% 2.89/1.06  --inst_start_prop_sim_after_learn       3
% 2.89/1.06  --inst_sel_renew                        solver
% 2.89/1.06  --inst_lit_activity_flag                true
% 2.89/1.06  --inst_restr_to_given                   false
% 2.89/1.06  --inst_activity_threshold               500
% 2.89/1.06  --inst_out_proof                        true
% 2.89/1.06  
% 2.89/1.06  ------ Resolution Options
% 2.89/1.06  
% 2.89/1.06  --resolution_flag                       true
% 2.89/1.06  --res_lit_sel                           adaptive
% 2.89/1.06  --res_lit_sel_side                      none
% 2.89/1.06  --res_ordering                          kbo
% 2.89/1.06  --res_to_prop_solver                    active
% 2.89/1.06  --res_prop_simpl_new                    false
% 2.89/1.06  --res_prop_simpl_given                  true
% 2.89/1.06  --res_passive_queue_type                priority_queues
% 2.89/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/1.06  --res_passive_queues_freq               [15;5]
% 2.89/1.06  --res_forward_subs                      full
% 2.89/1.06  --res_backward_subs                     full
% 2.89/1.06  --res_forward_subs_resolution           true
% 2.89/1.06  --res_backward_subs_resolution          true
% 2.89/1.06  --res_orphan_elimination                true
% 2.89/1.06  --res_time_limit                        2.
% 2.89/1.06  --res_out_proof                         true
% 2.89/1.06  
% 2.89/1.06  ------ Superposition Options
% 2.89/1.06  
% 2.89/1.06  --superposition_flag                    true
% 2.89/1.06  --sup_passive_queue_type                priority_queues
% 2.89/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.89/1.06  --demod_completeness_check              fast
% 2.89/1.06  --demod_use_ground                      true
% 2.89/1.06  --sup_to_prop_solver                    passive
% 2.89/1.06  --sup_prop_simpl_new                    true
% 2.89/1.06  --sup_prop_simpl_given                  true
% 2.89/1.06  --sup_fun_splitting                     false
% 2.89/1.06  --sup_smt_interval                      50000
% 2.89/1.06  
% 2.89/1.06  ------ Superposition Simplification Setup
% 2.89/1.06  
% 2.89/1.06  --sup_indices_passive                   []
% 2.89/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.06  --sup_full_bw                           [BwDemod]
% 2.89/1.06  --sup_immed_triv                        [TrivRules]
% 2.89/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.06  --sup_immed_bw_main                     []
% 2.89/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.06  
% 2.89/1.06  ------ Combination Options
% 2.89/1.06  
% 2.89/1.06  --comb_res_mult                         3
% 2.89/1.06  --comb_sup_mult                         2
% 2.89/1.06  --comb_inst_mult                        10
% 2.89/1.06  
% 2.89/1.06  ------ Debug Options
% 2.89/1.06  
% 2.89/1.06  --dbg_backtrace                         false
% 2.89/1.06  --dbg_dump_prop_clauses                 false
% 2.89/1.06  --dbg_dump_prop_clauses_file            -
% 2.89/1.06  --dbg_out_stat                          false
% 2.89/1.06  ------ Parsing...
% 2.89/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.89/1.06  
% 2.89/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.89/1.06  
% 2.89/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.89/1.06  
% 2.89/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.89/1.06  ------ Proving...
% 2.89/1.06  ------ Problem Properties 
% 2.89/1.06  
% 2.89/1.06  
% 2.89/1.06  clauses                                 42
% 2.89/1.06  conjectures                             13
% 2.89/1.06  EPR                                     10
% 2.89/1.06  Horn                                    35
% 2.89/1.06  unary                                   12
% 2.89/1.06  binary                                  11
% 2.89/1.06  lits                                    144
% 2.89/1.06  lits eq                                 2
% 2.89/1.06  fd_pure                                 0
% 2.89/1.06  fd_pseudo                               0
% 2.89/1.06  fd_cond                                 0
% 2.89/1.06  fd_pseudo_cond                          1
% 2.89/1.06  AC symbols                              0
% 2.89/1.06  
% 2.89/1.06  ------ Schedule dynamic 5 is on 
% 2.89/1.06  
% 2.89/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.89/1.06  
% 2.89/1.06  
% 2.89/1.06  ------ 
% 2.89/1.06  Current options:
% 2.89/1.06  ------ 
% 2.89/1.06  
% 2.89/1.06  ------ Input Options
% 2.89/1.06  
% 2.89/1.06  --out_options                           all
% 2.89/1.06  --tptp_safe_out                         true
% 2.89/1.06  --problem_path                          ""
% 2.89/1.06  --include_path                          ""
% 2.89/1.06  --clausifier                            res/vclausify_rel
% 2.89/1.06  --clausifier_options                    --mode clausify
% 2.89/1.06  --stdin                                 false
% 2.89/1.06  --stats_out                             all
% 2.89/1.06  
% 2.89/1.06  ------ General Options
% 2.89/1.06  
% 2.89/1.06  --fof                                   false
% 2.89/1.06  --time_out_real                         305.
% 2.89/1.06  --time_out_virtual                      -1.
% 2.89/1.06  --symbol_type_check                     false
% 2.89/1.06  --clausify_out                          false
% 2.89/1.06  --sig_cnt_out                           false
% 2.89/1.06  --trig_cnt_out                          false
% 2.89/1.06  --trig_cnt_out_tolerance                1.
% 2.89/1.06  --trig_cnt_out_sk_spl                   false
% 2.89/1.06  --abstr_cl_out                          false
% 2.89/1.06  
% 2.89/1.06  ------ Global Options
% 2.89/1.06  
% 2.89/1.06  --schedule                              default
% 2.89/1.06  --add_important_lit                     false
% 2.89/1.06  --prop_solver_per_cl                    1000
% 2.89/1.06  --min_unsat_core                        false
% 2.89/1.06  --soft_assumptions                      false
% 2.89/1.06  --soft_lemma_size                       3
% 2.89/1.06  --prop_impl_unit_size                   0
% 2.89/1.06  --prop_impl_unit                        []
% 2.89/1.06  --share_sel_clauses                     true
% 2.89/1.06  --reset_solvers                         false
% 2.89/1.06  --bc_imp_inh                            [conj_cone]
% 2.89/1.06  --conj_cone_tolerance                   3.
% 2.89/1.06  --extra_neg_conj                        none
% 2.89/1.06  --large_theory_mode                     true
% 2.89/1.06  --prolific_symb_bound                   200
% 2.89/1.06  --lt_threshold                          2000
% 2.89/1.06  --clause_weak_htbl                      true
% 2.89/1.06  --gc_record_bc_elim                     false
% 2.89/1.06  
% 2.89/1.06  ------ Preprocessing Options
% 2.89/1.06  
% 2.89/1.06  --preprocessing_flag                    true
% 2.89/1.06  --time_out_prep_mult                    0.1
% 2.89/1.06  --splitting_mode                        input
% 2.89/1.06  --splitting_grd                         true
% 2.89/1.06  --splitting_cvd                         false
% 2.89/1.06  --splitting_cvd_svl                     false
% 2.89/1.06  --splitting_nvd                         32
% 2.89/1.06  --sub_typing                            true
% 2.89/1.06  --prep_gs_sim                           true
% 2.89/1.06  --prep_unflatten                        true
% 2.89/1.06  --prep_res_sim                          true
% 2.89/1.06  --prep_upred                            true
% 2.89/1.06  --prep_sem_filter                       exhaustive
% 2.89/1.06  --prep_sem_filter_out                   false
% 2.89/1.06  --pred_elim                             true
% 2.89/1.06  --res_sim_input                         true
% 2.89/1.06  --eq_ax_congr_red                       true
% 2.89/1.06  --pure_diseq_elim                       true
% 2.89/1.06  --brand_transform                       false
% 2.89/1.06  --non_eq_to_eq                          false
% 2.89/1.06  --prep_def_merge                        true
% 2.89/1.06  --prep_def_merge_prop_impl              false
% 2.89/1.06  --prep_def_merge_mbd                    true
% 2.89/1.06  --prep_def_merge_tr_red                 false
% 2.89/1.06  --prep_def_merge_tr_cl                  false
% 2.89/1.06  --smt_preprocessing                     true
% 2.89/1.06  --smt_ac_axioms                         fast
% 2.89/1.06  --preprocessed_out                      false
% 2.89/1.06  --preprocessed_stats                    false
% 2.89/1.06  
% 2.89/1.06  ------ Abstraction refinement Options
% 2.89/1.06  
% 2.89/1.06  --abstr_ref                             []
% 2.89/1.06  --abstr_ref_prep                        false
% 2.89/1.06  --abstr_ref_until_sat                   false
% 2.89/1.06  --abstr_ref_sig_restrict                funpre
% 2.89/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/1.06  --abstr_ref_under                       []
% 2.89/1.06  
% 2.89/1.06  ------ SAT Options
% 2.89/1.06  
% 2.89/1.06  --sat_mode                              false
% 2.89/1.06  --sat_fm_restart_options                ""
% 2.89/1.06  --sat_gr_def                            false
% 2.89/1.06  --sat_epr_types                         true
% 2.89/1.06  --sat_non_cyclic_types                  false
% 2.89/1.06  --sat_finite_models                     false
% 2.89/1.06  --sat_fm_lemmas                         false
% 2.89/1.06  --sat_fm_prep                           false
% 2.89/1.06  --sat_fm_uc_incr                        true
% 2.89/1.06  --sat_out_model                         small
% 2.89/1.06  --sat_out_clauses                       false
% 2.89/1.06  
% 2.89/1.06  ------ QBF Options
% 2.89/1.06  
% 2.89/1.06  --qbf_mode                              false
% 2.89/1.06  --qbf_elim_univ                         false
% 2.89/1.06  --qbf_dom_inst                          none
% 2.89/1.06  --qbf_dom_pre_inst                      false
% 2.89/1.06  --qbf_sk_in                             false
% 2.89/1.06  --qbf_pred_elim                         true
% 2.89/1.06  --qbf_split                             512
% 2.89/1.06  
% 2.89/1.06  ------ BMC1 Options
% 2.89/1.06  
% 2.89/1.06  --bmc1_incremental                      false
% 2.89/1.06  --bmc1_axioms                           reachable_all
% 2.89/1.06  --bmc1_min_bound                        0
% 2.89/1.06  --bmc1_max_bound                        -1
% 2.89/1.06  --bmc1_max_bound_default                -1
% 2.89/1.06  --bmc1_symbol_reachability              true
% 2.89/1.06  --bmc1_property_lemmas                  false
% 2.89/1.06  --bmc1_k_induction                      false
% 2.89/1.06  --bmc1_non_equiv_states                 false
% 2.89/1.06  --bmc1_deadlock                         false
% 2.89/1.06  --bmc1_ucm                              false
% 2.89/1.06  --bmc1_add_unsat_core                   none
% 2.89/1.06  --bmc1_unsat_core_children              false
% 2.89/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/1.06  --bmc1_out_stat                         full
% 2.89/1.06  --bmc1_ground_init                      false
% 2.89/1.06  --bmc1_pre_inst_next_state              false
% 2.89/1.06  --bmc1_pre_inst_state                   false
% 2.89/1.06  --bmc1_pre_inst_reach_state             false
% 2.89/1.06  --bmc1_out_unsat_core                   false
% 2.89/1.06  --bmc1_aig_witness_out                  false
% 2.89/1.06  --bmc1_verbose                          false
% 2.89/1.06  --bmc1_dump_clauses_tptp                false
% 2.89/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.89/1.06  --bmc1_dump_file                        -
% 2.89/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.89/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.89/1.06  --bmc1_ucm_extend_mode                  1
% 2.89/1.06  --bmc1_ucm_init_mode                    2
% 2.89/1.06  --bmc1_ucm_cone_mode                    none
% 2.89/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.89/1.06  --bmc1_ucm_relax_model                  4
% 2.89/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.89/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/1.06  --bmc1_ucm_layered_model                none
% 2.89/1.06  --bmc1_ucm_max_lemma_size               10
% 2.89/1.06  
% 2.89/1.06  ------ AIG Options
% 2.89/1.06  
% 2.89/1.06  --aig_mode                              false
% 2.89/1.06  
% 2.89/1.06  ------ Instantiation Options
% 2.89/1.06  
% 2.89/1.06  --instantiation_flag                    true
% 2.89/1.06  --inst_sos_flag                         false
% 2.89/1.06  --inst_sos_phase                        true
% 2.89/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/1.06  --inst_lit_sel_side                     none
% 2.89/1.06  --inst_solver_per_active                1400
% 2.89/1.06  --inst_solver_calls_frac                1.
% 2.89/1.06  --inst_passive_queue_type               priority_queues
% 2.89/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/1.06  --inst_passive_queues_freq              [25;2]
% 2.89/1.06  --inst_dismatching                      true
% 2.89/1.06  --inst_eager_unprocessed_to_passive     true
% 2.89/1.06  --inst_prop_sim_given                   true
% 2.89/1.06  --inst_prop_sim_new                     false
% 2.89/1.06  --inst_subs_new                         false
% 2.89/1.06  --inst_eq_res_simp                      false
% 2.89/1.06  --inst_subs_given                       false
% 2.89/1.06  --inst_orphan_elimination               true
% 2.89/1.06  --inst_learning_loop_flag               true
% 2.89/1.06  --inst_learning_start                   3000
% 2.89/1.06  --inst_learning_factor                  2
% 2.89/1.06  --inst_start_prop_sim_after_learn       3
% 2.89/1.06  --inst_sel_renew                        solver
% 2.89/1.06  --inst_lit_activity_flag                true
% 2.89/1.06  --inst_restr_to_given                   false
% 2.89/1.06  --inst_activity_threshold               500
% 2.89/1.06  --inst_out_proof                        true
% 2.89/1.06  
% 2.89/1.06  ------ Resolution Options
% 2.89/1.06  
% 2.89/1.06  --resolution_flag                       false
% 2.89/1.06  --res_lit_sel                           adaptive
% 2.89/1.06  --res_lit_sel_side                      none
% 2.89/1.06  --res_ordering                          kbo
% 2.89/1.06  --res_to_prop_solver                    active
% 2.89/1.06  --res_prop_simpl_new                    false
% 2.89/1.06  --res_prop_simpl_given                  true
% 2.89/1.06  --res_passive_queue_type                priority_queues
% 2.89/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/1.06  --res_passive_queues_freq               [15;5]
% 2.89/1.06  --res_forward_subs                      full
% 2.89/1.06  --res_backward_subs                     full
% 2.89/1.06  --res_forward_subs_resolution           true
% 2.89/1.06  --res_backward_subs_resolution          true
% 2.89/1.06  --res_orphan_elimination                true
% 2.89/1.06  --res_time_limit                        2.
% 2.89/1.06  --res_out_proof                         true
% 2.89/1.06  
% 2.89/1.06  ------ Superposition Options
% 2.89/1.06  
% 2.89/1.06  --superposition_flag                    true
% 2.89/1.06  --sup_passive_queue_type                priority_queues
% 2.89/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.89/1.06  --demod_completeness_check              fast
% 2.89/1.06  --demod_use_ground                      true
% 2.89/1.06  --sup_to_prop_solver                    passive
% 2.89/1.06  --sup_prop_simpl_new                    true
% 2.89/1.06  --sup_prop_simpl_given                  true
% 2.89/1.06  --sup_fun_splitting                     false
% 2.89/1.06  --sup_smt_interval                      50000
% 2.89/1.06  
% 2.89/1.06  ------ Superposition Simplification Setup
% 2.89/1.06  
% 2.89/1.06  --sup_indices_passive                   []
% 2.89/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.06  --sup_full_bw                           [BwDemod]
% 2.89/1.06  --sup_immed_triv                        [TrivRules]
% 2.89/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.06  --sup_immed_bw_main                     []
% 2.89/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.06  
% 2.89/1.06  ------ Combination Options
% 2.89/1.06  
% 2.89/1.06  --comb_res_mult                         3
% 2.89/1.06  --comb_sup_mult                         2
% 2.89/1.06  --comb_inst_mult                        10
% 2.89/1.06  
% 2.89/1.06  ------ Debug Options
% 2.89/1.06  
% 2.89/1.06  --dbg_backtrace                         false
% 2.89/1.06  --dbg_dump_prop_clauses                 false
% 2.89/1.06  --dbg_dump_prop_clauses_file            -
% 2.89/1.06  --dbg_out_stat                          false
% 2.89/1.06  
% 2.89/1.06  
% 2.89/1.06  
% 2.89/1.06  
% 2.89/1.06  ------ Proving...
% 2.89/1.06  
% 2.89/1.06  
% 2.89/1.06  % SZS status Theorem for theBenchmark.p
% 2.89/1.06  
% 2.89/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 2.89/1.06  
% 2.89/1.06  fof(f11,conjecture,(
% 2.89/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.89/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.06  
% 2.89/1.06  fof(f12,negated_conjecture,(
% 2.89/1.06    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.89/1.06    inference(negated_conjecture,[],[f11])).
% 2.89/1.06  
% 2.89/1.06  fof(f29,plain,(
% 2.89/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.89/1.06    inference(ennf_transformation,[],[f12])).
% 2.89/1.06  
% 2.89/1.06  fof(f30,plain,(
% 2.89/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.89/1.06    inference(flattening,[],[f29])).
% 2.89/1.06  
% 2.89/1.06  fof(f51,plain,(
% 2.89/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.89/1.06    inference(nnf_transformation,[],[f30])).
% 2.89/1.06  
% 2.89/1.06  fof(f52,plain,(
% 2.89/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.89/1.06    inference(flattening,[],[f51])).
% 2.89/1.06  
% 2.89/1.06  fof(f56,plain,(
% 2.89/1.06    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK7 = X2 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK7))) )),
% 2.89/1.06    introduced(choice_axiom,[])).
% 2.89/1.06  
% 2.89/1.06  fof(f55,plain,(
% 2.89/1.06    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK6,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK6,X0,X1)) & sK6 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 2.89/1.06    introduced(choice_axiom,[])).
% 2.89/1.06  
% 2.89/1.06  fof(f54,plain,(
% 2.89/1.06    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(X2,X0,sK5)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(X2,X0,sK5)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK5)) & v1_funct_1(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5))) )),
% 2.89/1.06    introduced(choice_axiom,[])).
% 2.89/1.06  
% 2.89/1.06  fof(f53,plain,(
% 2.89/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK4,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK4,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 2.89/1.06    introduced(choice_axiom,[])).
% 2.89/1.06  
% 2.89/1.06  fof(f57,plain,(
% 2.89/1.06    ((((~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,sK5)) & (v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,sK5)) & sK6 = sK7 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 2.89/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f52,f56,f55,f54,f53])).
% 2.89/1.06  
% 2.89/1.06  fof(f91,plain,(
% 2.89/1.06    l1_pre_topc(sK5)),
% 2.89/1.06    inference(cnf_transformation,[],[f57])).
% 2.89/1.06  
% 2.89/1.06  fof(f1,axiom,(
% 2.89/1.06    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.89/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.06  
% 2.89/1.06  fof(f33,plain,(
% 2.89/1.06    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.89/1.06    inference(nnf_transformation,[],[f1])).
% 2.89/1.06  
% 2.89/1.06  fof(f34,plain,(
% 2.89/1.06    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.89/1.06    inference(flattening,[],[f33])).
% 2.89/1.06  
% 2.89/1.06  fof(f59,plain,(
% 2.89/1.06    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.89/1.06    inference(cnf_transformation,[],[f34])).
% 2.89/1.06  
% 2.89/1.06  fof(f101,plain,(
% 2.89/1.06    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.89/1.06    inference(equality_resolution,[],[f59])).
% 2.89/1.06  
% 2.89/1.06  fof(f2,axiom,(
% 2.89/1.06    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.89/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.06  
% 2.89/1.06  fof(f35,plain,(
% 2.89/1.06    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.89/1.06    inference(nnf_transformation,[],[f2])).
% 2.89/1.06  
% 2.89/1.06  fof(f62,plain,(
% 2.89/1.06    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.89/1.06    inference(cnf_transformation,[],[f35])).
% 2.89/1.06  
% 2.89/1.06  fof(f8,axiom,(
% 2.89/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.89/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.06  
% 2.89/1.06  fof(f23,plain,(
% 2.89/1.06    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.89/1.06    inference(ennf_transformation,[],[f8])).
% 2.89/1.06  
% 2.89/1.06  fof(f24,plain,(
% 2.89/1.06    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.89/1.06    inference(flattening,[],[f23])).
% 2.89/1.06  
% 2.89/1.06  fof(f47,plain,(
% 2.89/1.06    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.89/1.06    inference(nnf_transformation,[],[f24])).
% 2.89/1.06  
% 2.89/1.06  fof(f48,plain,(
% 2.89/1.06    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.89/1.06    inference(flattening,[],[f47])).
% 2.89/1.06  
% 2.89/1.06  fof(f83,plain,(
% 2.89/1.06    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.89/1.06    inference(cnf_transformation,[],[f48])).
% 2.89/1.06  
% 2.89/1.06  fof(f7,axiom,(
% 2.89/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.89/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.06  
% 2.89/1.06  fof(f14,plain,(
% 2.89/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 2.89/1.06    inference(pure_predicate_removal,[],[f7])).
% 2.89/1.06  
% 2.89/1.06  fof(f21,plain,(
% 2.89/1.06    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.89/1.06    inference(ennf_transformation,[],[f14])).
% 2.89/1.06  
% 2.89/1.06  fof(f22,plain,(
% 2.89/1.06    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.89/1.06    inference(flattening,[],[f21])).
% 2.89/1.06  
% 2.89/1.06  fof(f79,plain,(
% 2.89/1.06    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.89/1.06    inference(cnf_transformation,[],[f22])).
% 2.89/1.06  
% 2.89/1.06  fof(f6,axiom,(
% 2.89/1.06    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.89/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.06  
% 2.89/1.06  fof(f20,plain,(
% 2.89/1.06    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.89/1.06    inference(ennf_transformation,[],[f6])).
% 2.89/1.06  
% 2.89/1.06  fof(f78,plain,(
% 2.89/1.06    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.89/1.06    inference(cnf_transformation,[],[f20])).
% 2.89/1.06  
% 2.89/1.06  fof(f5,axiom,(
% 2.89/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.89/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.06  
% 2.89/1.06  fof(f15,plain,(
% 2.89/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 2.89/1.06    inference(pure_predicate_removal,[],[f5])).
% 2.89/1.06  
% 2.89/1.06  fof(f19,plain,(
% 2.89/1.06    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.89/1.06    inference(ennf_transformation,[],[f15])).
% 2.89/1.06  
% 2.89/1.06  fof(f77,plain,(
% 2.89/1.06    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.89/1.06    inference(cnf_transformation,[],[f19])).
% 2.89/1.06  
% 2.89/1.06  fof(f4,axiom,(
% 2.89/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.89/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.06  
% 2.89/1.06  fof(f18,plain,(
% 2.89/1.06    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.89/1.06    inference(ennf_transformation,[],[f4])).
% 2.89/1.06  
% 2.89/1.06  fof(f46,plain,(
% 2.89/1.06    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.89/1.06    inference(nnf_transformation,[],[f18])).
% 2.89/1.06  
% 2.89/1.06  fof(f76,plain,(
% 2.89/1.06    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.89/1.06    inference(cnf_transformation,[],[f46])).
% 2.89/1.06  
% 2.89/1.06  fof(f3,axiom,(
% 2.89/1.06    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.89/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.06  
% 2.89/1.06  fof(f13,plain,(
% 2.89/1.06    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.89/1.06    inference(rectify,[],[f3])).
% 2.89/1.06  
% 2.89/1.06  fof(f16,plain,(
% 2.89/1.06    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.89/1.06    inference(ennf_transformation,[],[f13])).
% 2.89/1.06  
% 2.89/1.06  fof(f17,plain,(
% 2.89/1.06    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.89/1.06    inference(flattening,[],[f16])).
% 2.89/1.06  
% 2.89/1.06  fof(f31,plain,(
% 2.89/1.06    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.89/1.06    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.89/1.06  
% 2.89/1.06  fof(f32,plain,(
% 2.89/1.06    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.89/1.06    inference(definition_folding,[],[f17,f31])).
% 2.89/1.06  
% 2.89/1.06  fof(f41,plain,(
% 2.89/1.06    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.89/1.06    inference(nnf_transformation,[],[f32])).
% 2.89/1.06  
% 2.89/1.06  fof(f42,plain,(
% 2.89/1.06    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.89/1.06    inference(flattening,[],[f41])).
% 2.89/1.06  
% 2.89/1.06  fof(f43,plain,(
% 2.89/1.06    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.89/1.06    inference(rectify,[],[f42])).
% 2.89/1.06  
% 2.89/1.06  fof(f44,plain,(
% 2.89/1.06    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.89/1.06    introduced(choice_axiom,[])).
% 2.89/1.06  
% 2.89/1.06  fof(f45,plain,(
% 2.89/1.06    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.89/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 2.89/1.06  
% 2.89/1.06  fof(f69,plain,(
% 2.89/1.06    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.89/1.06    inference(cnf_transformation,[],[f45])).
% 2.89/1.06  
% 2.89/1.06  fof(f61,plain,(
% 2.89/1.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.89/1.06    inference(cnf_transformation,[],[f35])).
% 2.89/1.06  
% 2.89/1.06  fof(f60,plain,(
% 2.89/1.06    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.89/1.06    inference(cnf_transformation,[],[f34])).
% 2.89/1.06  
% 2.89/1.06  fof(f81,plain,(
% 2.89/1.06    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.89/1.06    inference(cnf_transformation,[],[f48])).
% 2.89/1.06  
% 2.89/1.06  fof(f90,plain,(
% 2.89/1.06    v2_pre_topc(sK5)),
% 2.89/1.06    inference(cnf_transformation,[],[f57])).
% 2.89/1.06  
% 2.89/1.06  fof(f97,plain,(
% 2.89/1.06    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))),
% 2.89/1.06    inference(cnf_transformation,[],[f57])).
% 2.89/1.06  
% 2.89/1.06  fof(f9,axiom,(
% 2.89/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.89/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.06  
% 2.89/1.06  fof(f25,plain,(
% 2.89/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.89/1.06    inference(ennf_transformation,[],[f9])).
% 2.89/1.06  
% 2.89/1.06  fof(f26,plain,(
% 2.89/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.89/1.06    inference(flattening,[],[f25])).
% 2.89/1.06  
% 2.89/1.06  fof(f49,plain,(
% 2.89/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.89/1.06    inference(nnf_transformation,[],[f26])).
% 2.89/1.06  
% 2.89/1.06  fof(f85,plain,(
% 2.89/1.06    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.89/1.06    inference(cnf_transformation,[],[f49])).
% 2.89/1.06  
% 2.89/1.06  fof(f103,plain,(
% 2.89/1.06    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.89/1.06    inference(equality_resolution,[],[f85])).
% 2.89/1.06  
% 2.89/1.06  fof(f99,plain,(
% 2.89/1.06    v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,sK5)),
% 2.89/1.06    inference(cnf_transformation,[],[f57])).
% 2.89/1.06  
% 2.89/1.06  fof(f98,plain,(
% 2.89/1.06    sK6 = sK7),
% 2.89/1.06    inference(cnf_transformation,[],[f57])).
% 2.89/1.06  
% 2.89/1.06  fof(f10,axiom,(
% 2.89/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.89/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.06  
% 2.89/1.06  fof(f27,plain,(
% 2.89/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.89/1.06    inference(ennf_transformation,[],[f10])).
% 2.89/1.06  
% 2.89/1.06  fof(f28,plain,(
% 2.89/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.89/1.06    inference(flattening,[],[f27])).
% 2.89/1.06  
% 2.89/1.06  fof(f50,plain,(
% 2.89/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.89/1.06    inference(nnf_transformation,[],[f28])).
% 2.89/1.06  
% 2.89/1.06  fof(f87,plain,(
% 2.89/1.06    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.89/1.06    inference(cnf_transformation,[],[f50])).
% 2.89/1.06  
% 2.89/1.06  fof(f105,plain,(
% 2.89/1.06    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.89/1.06    inference(equality_resolution,[],[f87])).
% 2.89/1.06  
% 2.89/1.06  fof(f88,plain,(
% 2.89/1.06    v2_pre_topc(sK4)),
% 2.89/1.06    inference(cnf_transformation,[],[f57])).
% 2.89/1.06  
% 2.89/1.06  fof(f89,plain,(
% 2.89/1.06    l1_pre_topc(sK4)),
% 2.89/1.06    inference(cnf_transformation,[],[f57])).
% 2.89/1.06  
% 2.89/1.06  fof(f95,plain,(
% 2.89/1.06    v1_funct_1(sK7)),
% 2.89/1.06    inference(cnf_transformation,[],[f57])).
% 2.89/1.06  
% 2.89/1.06  fof(f96,plain,(
% 2.89/1.06    v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 2.89/1.06    inference(cnf_transformation,[],[f57])).
% 2.89/1.06  
% 2.89/1.06  fof(f84,plain,(
% 2.89/1.06    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.89/1.06    inference(cnf_transformation,[],[f49])).
% 2.89/1.06  
% 2.89/1.06  fof(f104,plain,(
% 2.89/1.06    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.89/1.06    inference(equality_resolution,[],[f84])).
% 2.89/1.06  
% 2.89/1.06  fof(f86,plain,(
% 2.89/1.06    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.89/1.06    inference(cnf_transformation,[],[f50])).
% 2.89/1.06  
% 2.89/1.06  fof(f106,plain,(
% 2.89/1.06    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.89/1.06    inference(equality_resolution,[],[f86])).
% 2.89/1.06  
% 2.89/1.06  fof(f100,plain,(
% 2.89/1.06    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,sK5)),
% 2.89/1.06    inference(cnf_transformation,[],[f57])).
% 2.89/1.06  
% 2.89/1.06  fof(f94,plain,(
% 2.89/1.06    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))),
% 2.89/1.06    inference(cnf_transformation,[],[f57])).
% 2.89/1.06  
% 2.89/1.06  fof(f93,plain,(
% 2.89/1.06    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))),
% 2.89/1.06    inference(cnf_transformation,[],[f57])).
% 2.89/1.06  
% 2.89/1.06  cnf(c_39,negated_conjecture,
% 2.89/1.06      ( l1_pre_topc(sK5) ),
% 2.89/1.06      inference(cnf_transformation,[],[f91]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3669,plain,
% 2.89/1.06      ( l1_pre_topc(sK5) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_1,plain,
% 2.89/1.06      ( r1_tarski(X0,X0) ),
% 2.89/1.06      inference(cnf_transformation,[],[f101]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3705,plain,
% 2.89/1.06      ( r1_tarski(X0,X0) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3,plain,
% 2.89/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.89/1.06      inference(cnf_transformation,[],[f62]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3704,plain,
% 2.89/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.89/1.06      | r1_tarski(X0,X1) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_22,plain,
% 2.89/1.06      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.89/1.06      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.89/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 2.89/1.06      | ~ l1_pre_topc(X1)
% 2.89/1.06      | ~ v2_pre_topc(X1) ),
% 2.89/1.06      inference(cnf_transformation,[],[f83]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3685,plain,
% 2.89/1.06      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 2.89/1.06      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 2.89/1.06      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 2.89/1.06      | l1_pre_topc(X1) != iProver_top
% 2.89/1.06      | v2_pre_topc(X1) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_7528,plain,
% 2.89/1.06      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 2.89/1.06      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 2.89/1.06      | r1_tarski(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 2.89/1.06      | l1_pre_topc(X1) != iProver_top
% 2.89/1.06      | v2_pre_topc(X1) != iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_3704,c_3685]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_8211,plain,
% 2.89/1.06      ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 2.89/1.06      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 2.89/1.06      | l1_pre_topc(X0) != iProver_top
% 2.89/1.06      | v2_pre_topc(X0) != iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_3705,c_7528]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_21,plain,
% 2.89/1.06      ( ~ l1_pre_topc(X0)
% 2.89/1.06      | ~ v2_pre_topc(X0)
% 2.89/1.06      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.89/1.06      inference(cnf_transformation,[],[f79]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_79,plain,
% 2.89/1.06      ( l1_pre_topc(X0) != iProver_top
% 2.89/1.06      | v2_pre_topc(X0) != iProver_top
% 2.89/1.06      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_20,plain,
% 2.89/1.06      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.89/1.06      | ~ l1_pre_topc(X0) ),
% 2.89/1.06      inference(cnf_transformation,[],[f78]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3687,plain,
% 2.89/1.06      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.89/1.06      | l1_pre_topc(X0) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_19,plain,
% 2.89/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.89/1.06      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 2.89/1.06      inference(cnf_transformation,[],[f77]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3688,plain,
% 2.89/1.06      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.89/1.06      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_4810,plain,
% 2.89/1.06      ( l1_pre_topc(X0) != iProver_top
% 2.89/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_3687,c_3688]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_17,plain,
% 2.89/1.06      ( v3_pre_topc(X0,X1)
% 2.89/1.06      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.89/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.89/1.06      | ~ l1_pre_topc(X1) ),
% 2.89/1.06      inference(cnf_transformation,[],[f76]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_4119,plain,
% 2.89/1.06      ( v3_pre_topc(u1_struct_0(X0),X0)
% 2.89/1.06      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 2.89/1.06      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.89/1.06      | ~ l1_pre_topc(X0) ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_17]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_5237,plain,
% 2.89/1.06      ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.89/1.06      | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
% 2.89/1.06      | ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
% 2.89/1.06      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_4119]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_5240,plain,
% 2.89/1.06      ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 2.89/1.06      | r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 2.89/1.06      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) != iProver_top
% 2.89/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_5237]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_5239,plain,
% 2.89/1.06      ( ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.89/1.06      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0)))
% 2.89/1.06      | ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
% 2.89/1.06      | ~ l1_pre_topc(X0)
% 2.89/1.06      | ~ v2_pre_topc(X0) ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_22]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_5244,plain,
% 2.89/1.06      ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 2.89/1.06      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 2.89/1.06      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) != iProver_top
% 2.89/1.06      | l1_pre_topc(X0) != iProver_top
% 2.89/1.06      | v2_pre_topc(X0) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_5239]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_16,plain,
% 2.89/1.06      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 2.89/1.06      | ~ l1_pre_topc(X0)
% 2.89/1.06      | ~ v2_pre_topc(X0) ),
% 2.89/1.06      inference(cnf_transformation,[],[f69]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_6336,plain,
% 2.89/1.06      ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
% 2.89/1.06      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.89/1.06      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_16]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_6337,plain,
% 2.89/1.06      ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = iProver_top
% 2.89/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 2.89/1.06      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_6336]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_4319,plain,
% 2.89/1.06      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.89/1.06      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_3]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_7010,plain,
% 2.89/1.06      ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
% 2.89/1.06      | ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_4319]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_7011,plain,
% 2.89/1.06      ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) = iProver_top
% 2.89/1.06      | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_7010]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_4620,plain,
% 2.89/1.06      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_1]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_8131,plain,
% 2.89/1.06      ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_4620]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_8132,plain,
% 2.89/1.06      ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_8131]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_8227,plain,
% 2.89/1.06      ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 2.89/1.06      | l1_pre_topc(X0) != iProver_top
% 2.89/1.06      | v2_pre_topc(X0) != iProver_top ),
% 2.89/1.06      inference(global_propositional_subsumption,
% 2.89/1.06                [status(thm)],
% 2.89/1.06                [c_8211,c_79,c_4810,c_5240,c_5244,c_6337,c_7011,c_8132]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_4,plain,
% 2.89/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.89/1.06      inference(cnf_transformation,[],[f61]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3703,plain,
% 2.89/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.89/1.06      | r1_tarski(X0,X1) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_8236,plain,
% 2.89/1.06      ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X0)) = iProver_top
% 2.89/1.06      | l1_pre_topc(X0) != iProver_top
% 2.89/1.06      | v2_pre_topc(X0) != iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_8227,c_3703]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_0,plain,
% 2.89/1.06      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.89/1.06      inference(cnf_transformation,[],[f60]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3706,plain,
% 2.89/1.06      ( X0 = X1
% 2.89/1.06      | r1_tarski(X0,X1) != iProver_top
% 2.89/1.06      | r1_tarski(X1,X0) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_8410,plain,
% 2.89/1.06      ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0)
% 2.89/1.06      | r1_tarski(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 2.89/1.06      | l1_pre_topc(X0) != iProver_top
% 2.89/1.06      | v2_pre_topc(X0) != iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_8236,c_3706]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_4320,plain,
% 2.89/1.06      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 2.89/1.06      | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_4319]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_4621,plain,
% 2.89/1.06      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_4620]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_24,plain,
% 2.89/1.06      ( ~ v3_pre_topc(X0,X1)
% 2.89/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.89/1.06      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 2.89/1.06      | ~ l1_pre_topc(X1)
% 2.89/1.06      | ~ v2_pre_topc(X1) ),
% 2.89/1.06      inference(cnf_transformation,[],[f81]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_5220,plain,
% 2.89/1.06      ( ~ v3_pre_topc(u1_struct_0(X0),X0)
% 2.89/1.06      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.89/1.06      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
% 2.89/1.06      | ~ l1_pre_topc(X0)
% 2.89/1.06      | ~ v2_pre_topc(X0) ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_24]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_5229,plain,
% 2.89/1.06      ( v3_pre_topc(u1_struct_0(X0),X0) != iProver_top
% 2.89/1.06      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.89/1.06      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) = iProver_top
% 2.89/1.06      | l1_pre_topc(X0) != iProver_top
% 2.89/1.06      | v2_pre_topc(X0) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_5220]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_6033,plain,
% 2.89/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.89/1.06      | r1_tarski(X0,u1_struct_0(X1)) ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_4]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_7156,plain,
% 2.89/1.06      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
% 2.89/1.06      | r1_tarski(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_6033]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_7157,plain,
% 2.89/1.06      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) != iProver_top
% 2.89/1.06      | r1_tarski(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_7156]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3691,plain,
% 2.89/1.06      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 2.89/1.06      | l1_pre_topc(X0) != iProver_top
% 2.89/1.06      | v2_pre_topc(X0) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3690,plain,
% 2.89/1.06      ( v3_pre_topc(X0,X1) = iProver_top
% 2.89/1.06      | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 2.89/1.06      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.89/1.06      | l1_pre_topc(X1) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_6130,plain,
% 2.89/1.06      ( v3_pre_topc(X0,X1) = iProver_top
% 2.89/1.06      | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 2.89/1.06      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 2.89/1.06      | l1_pre_topc(X1) != iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_3704,c_3690]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_7341,plain,
% 2.89/1.06      ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
% 2.89/1.06      | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top
% 2.89/1.06      | l1_pre_topc(X0) != iProver_top
% 2.89/1.06      | v2_pre_topc(X0) != iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_3691,c_6130]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_8426,plain,
% 2.89/1.06      ( u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0)
% 2.89/1.06      | l1_pre_topc(X0) != iProver_top
% 2.89/1.06      | v2_pre_topc(X0) != iProver_top ),
% 2.89/1.06      inference(global_propositional_subsumption,
% 2.89/1.06                [status(thm)],
% 2.89/1.06                [c_8410,c_4320,c_4621,c_5229,c_7157,c_7341]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_8435,plain,
% 2.89/1.06      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
% 2.89/1.06      | v2_pre_topc(sK5) != iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_3669,c_8426]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_40,negated_conjecture,
% 2.89/1.06      ( v2_pre_topc(sK5) ),
% 2.89/1.06      inference(cnf_transformation,[],[f90]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_45,plain,
% 2.89/1.06      ( v2_pre_topc(sK5) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_8612,plain,
% 2.89/1.06      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5) ),
% 2.89/1.06      inference(global_propositional_subsumption,
% 2.89/1.06                [status(thm)],
% 2.89/1.06                [c_8435,c_45]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_33,negated_conjecture,
% 2.89/1.06      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) ),
% 2.89/1.06      inference(cnf_transformation,[],[f97]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3675,plain,
% 2.89/1.06      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_8627,plain,
% 2.89/1.06      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) = iProver_top ),
% 2.89/1.06      inference(demodulation,[status(thm)],[c_8612,c_3675]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_26,plain,
% 2.89/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.89/1.06      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 2.89/1.06      | v5_pre_topc(X0,X1,X2)
% 2.89/1.06      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 2.89/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.89/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 2.89/1.06      | ~ v1_funct_1(X0)
% 2.89/1.06      | ~ l1_pre_topc(X1)
% 2.89/1.06      | ~ l1_pre_topc(X2)
% 2.89/1.06      | ~ v2_pre_topc(X1)
% 2.89/1.06      | ~ v2_pre_topc(X2) ),
% 2.89/1.06      inference(cnf_transformation,[],[f103]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3681,plain,
% 2.89/1.06      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 2.89/1.06      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 2.89/1.06      | v5_pre_topc(X0,X1,X2) = iProver_top
% 2.89/1.06      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 2.89/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 2.89/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 2.89/1.06      | v1_funct_1(X0) != iProver_top
% 2.89/1.06      | l1_pre_topc(X1) != iProver_top
% 2.89/1.06      | l1_pre_topc(X2) != iProver_top
% 2.89/1.06      | v2_pre_topc(X1) != iProver_top
% 2.89/1.06      | v2_pre_topc(X2) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_9613,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,sK4,sK5) = iProver_top
% 2.89/1.06      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
% 2.89/1.06      | v1_funct_1(sK7) != iProver_top
% 2.89/1.06      | l1_pre_topc(sK5) != iProver_top
% 2.89/1.06      | l1_pre_topc(sK4) != iProver_top
% 2.89/1.06      | v2_pre_topc(sK5) != iProver_top
% 2.89/1.06      | v2_pre_topc(sK4) != iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_8627,c_3681]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_31,negated_conjecture,
% 2.89/1.06      ( v5_pre_topc(sK6,sK4,sK5)
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
% 2.89/1.06      inference(cnf_transformation,[],[f99]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3676,plain,
% 2.89/1.06      ( v5_pre_topc(sK6,sK4,sK5) = iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_32,negated_conjecture,
% 2.89/1.06      ( sK6 = sK7 ),
% 2.89/1.06      inference(cnf_transformation,[],[f98]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3792,plain,
% 2.89/1.06      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,sK4,sK5) = iProver_top ),
% 2.89/1.06      inference(light_normalisation,[status(thm)],[c_3676,c_32]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_28,plain,
% 2.89/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.89/1.06      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 2.89/1.06      | v5_pre_topc(X0,X1,X2)
% 2.89/1.06      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 2.89/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.89/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 2.89/1.06      | ~ v1_funct_1(X0)
% 2.89/1.06      | ~ l1_pre_topc(X1)
% 2.89/1.06      | ~ l1_pre_topc(X2)
% 2.89/1.06      | ~ v2_pre_topc(X1)
% 2.89/1.06      | ~ v2_pre_topc(X2) ),
% 2.89/1.06      inference(cnf_transformation,[],[f105]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3679,plain,
% 2.89/1.06      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 2.89/1.06      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 2.89/1.06      | v5_pre_topc(X0,X1,X2) = iProver_top
% 2.89/1.06      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 2.89/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 2.89/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 2.89/1.06      | v1_funct_1(X0) != iProver_top
% 2.89/1.06      | l1_pre_topc(X1) != iProver_top
% 2.89/1.06      | l1_pre_topc(X2) != iProver_top
% 2.89/1.06      | v2_pre_topc(X1) != iProver_top
% 2.89/1.06      | v2_pre_topc(X2) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_5384,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 2.89/1.06      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
% 2.89/1.06      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top
% 2.89/1.06      | v1_funct_1(sK7) != iProver_top
% 2.89/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 2.89/1.06      | l1_pre_topc(sK5) != iProver_top
% 2.89/1.06      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 2.89/1.06      | v2_pre_topc(sK5) != iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_3675,c_3679]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_42,negated_conjecture,
% 2.89/1.06      ( v2_pre_topc(sK4) ),
% 2.89/1.06      inference(cnf_transformation,[],[f88]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_43,plain,
% 2.89/1.06      ( v2_pre_topc(sK4) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_41,negated_conjecture,
% 2.89/1.06      ( l1_pre_topc(sK4) ),
% 2.89/1.06      inference(cnf_transformation,[],[f89]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_44,plain,
% 2.89/1.06      ( l1_pre_topc(sK4) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_46,plain,
% 2.89/1.06      ( l1_pre_topc(sK5) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_35,negated_conjecture,
% 2.89/1.06      ( v1_funct_1(sK7) ),
% 2.89/1.06      inference(cnf_transformation,[],[f95]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_50,plain,
% 2.89/1.06      ( v1_funct_1(sK7) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_34,negated_conjecture,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
% 2.89/1.06      inference(cnf_transformation,[],[f96]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_51,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_81,plain,
% 2.89/1.06      ( l1_pre_topc(sK4) != iProver_top
% 2.89/1.06      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 2.89/1.06      | v2_pre_topc(sK4) != iProver_top ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_79]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_82,plain,
% 2.89/1.06      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.89/1.06      | l1_pre_topc(X0) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_84,plain,
% 2.89/1.06      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
% 2.89/1.06      | l1_pre_topc(sK4) != iProver_top ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_82]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_4100,plain,
% 2.89/1.06      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.89/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_19]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_4101,plain,
% 2.89/1.06      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 2.89/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_4100]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_4103,plain,
% 2.89/1.06      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 2.89/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 2.89/1.06      inference(instantiation,[status(thm)],[c_4101]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_5613,plain,
% 2.89/1.06      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 2.89/1.06      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top ),
% 2.89/1.06      inference(global_propositional_subsumption,
% 2.89/1.06                [status(thm)],
% 2.89/1.06                [c_5384,c_43,c_44,c_45,c_46,c_50,c_51,c_81,c_84,c_4103]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_5614,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
% 2.89/1.06      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top ),
% 2.89/1.06      inference(renaming,[status(thm)],[c_5613]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_5622,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,sK4,sK5) = iProver_top
% 2.89/1.06      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_3792,c_5614]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_9615,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,sK4,sK5) = iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_8627,c_5622]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_9659,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,sK4,sK5) = iProver_top
% 2.89/1.06      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
% 2.89/1.06      | v1_funct_1(sK7) != iProver_top
% 2.89/1.06      | l1_pre_topc(sK5) != iProver_top
% 2.89/1.06      | l1_pre_topc(sK4) != iProver_top
% 2.89/1.06      | v2_pre_topc(sK5) != iProver_top
% 2.89/1.06      | v2_pre_topc(sK4) != iProver_top ),
% 2.89/1.06      inference(forward_subsumption_resolution,
% 2.89/1.06                [status(thm)],
% 2.89/1.06                [c_9613,c_9615]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_27,plain,
% 2.89/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.89/1.06      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 2.89/1.06      | ~ v5_pre_topc(X0,X1,X2)
% 2.89/1.06      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 2.89/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.89/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 2.89/1.06      | ~ v1_funct_1(X0)
% 2.89/1.06      | ~ l1_pre_topc(X1)
% 2.89/1.06      | ~ l1_pre_topc(X2)
% 2.89/1.06      | ~ v2_pre_topc(X1)
% 2.89/1.06      | ~ v2_pre_topc(X2) ),
% 2.89/1.06      inference(cnf_transformation,[],[f104]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3680,plain,
% 2.89/1.06      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 2.89/1.06      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 2.89/1.06      | v5_pre_topc(X0,X1,X2) != iProver_top
% 2.89/1.06      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 2.89/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 2.89/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 2.89/1.06      | v1_funct_1(X0) != iProver_top
% 2.89/1.06      | l1_pre_topc(X1) != iProver_top
% 2.89/1.06      | l1_pre_topc(X2) != iProver_top
% 2.89/1.06      | v2_pre_topc(X1) != iProver_top
% 2.89/1.06      | v2_pre_topc(X2) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_9614,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,sK4,sK5) != iProver_top
% 2.89/1.06      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
% 2.89/1.06      | v1_funct_1(sK7) != iProver_top
% 2.89/1.06      | l1_pre_topc(sK5) != iProver_top
% 2.89/1.06      | l1_pre_topc(sK4) != iProver_top
% 2.89/1.06      | v2_pre_topc(sK5) != iProver_top
% 2.89/1.06      | v2_pre_topc(sK4) != iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_8627,c_3680]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_9639,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
% 2.89/1.06      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
% 2.89/1.06      | v1_funct_1(sK7) != iProver_top
% 2.89/1.06      | l1_pre_topc(sK5) != iProver_top
% 2.89/1.06      | l1_pre_topc(sK4) != iProver_top
% 2.89/1.06      | v2_pre_topc(sK5) != iProver_top
% 2.89/1.06      | v2_pre_topc(sK4) != iProver_top ),
% 2.89/1.06      inference(forward_subsumption_resolution,
% 2.89/1.06                [status(thm)],
% 2.89/1.06                [c_9614,c_9615]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3674,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_8628,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) = iProver_top ),
% 2.89/1.06      inference(demodulation,[status(thm)],[c_8612,c_3674]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_4451,plain,
% 2.89/1.06      ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))) = iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_3675,c_3703]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_8626,plain,
% 2.89/1.06      ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))) = iProver_top ),
% 2.89/1.06      inference(demodulation,[status(thm)],[c_8612,c_4451]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_29,plain,
% 2.89/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.89/1.06      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 2.89/1.06      | ~ v5_pre_topc(X0,X1,X2)
% 2.89/1.06      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 2.89/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.89/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 2.89/1.06      | ~ v1_funct_1(X0)
% 2.89/1.06      | ~ l1_pre_topc(X1)
% 2.89/1.06      | ~ l1_pre_topc(X2)
% 2.89/1.06      | ~ v2_pre_topc(X1)
% 2.89/1.06      | ~ v2_pre_topc(X2) ),
% 2.89/1.06      inference(cnf_transformation,[],[f106]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3678,plain,
% 2.89/1.06      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 2.89/1.06      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 2.89/1.06      | v5_pre_topc(X0,X1,X2) != iProver_top
% 2.89/1.06      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 2.89/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 2.89/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 2.89/1.06      | v1_funct_1(X0) != iProver_top
% 2.89/1.06      | l1_pre_topc(X1) != iProver_top
% 2.89/1.06      | l1_pre_topc(X2) != iProver_top
% 2.89/1.06      | v2_pre_topc(X1) != iProver_top
% 2.89/1.06      | v2_pre_topc(X2) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_4659,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 2.89/1.06      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
% 2.89/1.06      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top
% 2.89/1.06      | v1_funct_1(sK7) != iProver_top
% 2.89/1.06      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 2.89/1.06      | l1_pre_topc(sK5) != iProver_top
% 2.89/1.06      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 2.89/1.06      | v2_pre_topc(sK5) != iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_3675,c_3678]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_5014,plain,
% 2.89/1.06      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 2.89/1.06      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top ),
% 2.89/1.06      inference(global_propositional_subsumption,
% 2.89/1.06                [status(thm)],
% 2.89/1.06                [c_4659,c_43,c_44,c_45,c_46,c_50,c_51,c_81,c_84,c_4103]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_5015,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
% 2.89/1.06      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top ),
% 2.89/1.06      inference(renaming,[status(thm)],[c_5014]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_5022,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
% 2.89/1.06      | r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))) != iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_3704,c_5015]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_30,negated_conjecture,
% 2.89/1.06      ( ~ v5_pre_topc(sK6,sK4,sK5)
% 2.89/1.06      | ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
% 2.89/1.06      inference(cnf_transformation,[],[f100]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3677,plain,
% 2.89/1.06      ( v5_pre_topc(sK6,sK4,sK5) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3797,plain,
% 2.89/1.06      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,sK4,sK5) != iProver_top ),
% 2.89/1.06      inference(light_normalisation,[status(thm)],[c_3677,c_32]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_5101,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
% 2.89/1.06      | v5_pre_topc(sK7,sK4,sK5) != iProver_top
% 2.89/1.06      | r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))) != iProver_top ),
% 2.89/1.06      inference(superposition,[status(thm)],[c_5022,c_3797]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_36,negated_conjecture,
% 2.89/1.06      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
% 2.89/1.06      inference(cnf_transformation,[],[f94]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3672,plain,
% 2.89/1.06      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3725,plain,
% 2.89/1.06      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
% 2.89/1.06      inference(light_normalisation,[status(thm)],[c_3672,c_32]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_37,negated_conjecture,
% 2.89/1.06      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
% 2.89/1.06      inference(cnf_transformation,[],[f93]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3671,plain,
% 2.89/1.06      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) = iProver_top ),
% 2.89/1.06      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(c_3722,plain,
% 2.89/1.06      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) = iProver_top ),
% 2.89/1.06      inference(light_normalisation,[status(thm)],[c_3671,c_32]) ).
% 2.89/1.06  
% 2.89/1.06  cnf(contradiction,plain,
% 2.89/1.06      ( $false ),
% 2.89/1.06      inference(minisat,
% 2.89/1.06                [status(thm)],
% 2.89/1.06                [c_9659,c_9639,c_8628,c_8626,c_5101,c_3725,c_3722,c_50,
% 2.89/1.06                 c_46,c_45,c_44,c_43]) ).
% 2.89/1.06  
% 2.89/1.06  
% 2.89/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 2.89/1.06  
% 2.89/1.06  ------                               Statistics
% 2.89/1.06  
% 2.89/1.06  ------ General
% 2.89/1.06  
% 2.89/1.06  abstr_ref_over_cycles:                  0
% 2.89/1.06  abstr_ref_under_cycles:                 0
% 2.89/1.06  gc_basic_clause_elim:                   0
% 2.89/1.06  forced_gc_time:                         0
% 2.89/1.06  parsing_time:                           0.05
% 2.89/1.06  unif_index_cands_time:                  0.
% 2.89/1.06  unif_index_add_time:                    0.
% 2.89/1.06  orderings_time:                         0.
% 2.89/1.06  out_proof_time:                         0.011
% 2.89/1.06  total_time:                             0.273
% 2.89/1.06  num_of_symbols:                         55
% 2.89/1.06  num_of_terms:                           5075
% 2.89/1.06  
% 2.89/1.06  ------ Preprocessing
% 2.89/1.06  
% 2.89/1.06  num_of_splits:                          0
% 2.89/1.06  num_of_split_atoms:                     0
% 2.89/1.06  num_of_reused_defs:                     0
% 2.89/1.06  num_eq_ax_congr_red:                    15
% 2.89/1.06  num_of_sem_filtered_clauses:            1
% 2.89/1.06  num_of_subtypes:                        0
% 2.89/1.06  monotx_restored_types:                  0
% 2.89/1.06  sat_num_of_epr_types:                   0
% 2.89/1.06  sat_num_of_non_cyclic_types:            0
% 2.89/1.06  sat_guarded_non_collapsed_types:        0
% 2.89/1.06  num_pure_diseq_elim:                    0
% 2.89/1.06  simp_replaced_by:                       0
% 2.89/1.06  res_preprocessed:                       205
% 2.89/1.06  prep_upred:                             0
% 2.89/1.06  prep_unflattend:                        28
% 2.89/1.06  smt_new_axioms:                         0
% 2.89/1.06  pred_elim_cands:                        10
% 2.89/1.06  pred_elim:                              0
% 2.89/1.06  pred_elim_cl:                           0
% 2.89/1.06  pred_elim_cycles:                       4
% 2.89/1.06  merged_defs:                            16
% 2.89/1.06  merged_defs_ncl:                        0
% 2.89/1.06  bin_hyper_res:                          16
% 2.89/1.06  prep_cycles:                            4
% 2.89/1.06  pred_elim_time:                         0.024
% 2.89/1.06  splitting_time:                         0.
% 2.89/1.06  sem_filter_time:                        0.
% 2.89/1.06  monotx_time:                            0.
% 2.89/1.06  subtype_inf_time:                       0.
% 2.89/1.06  
% 2.89/1.06  ------ Problem properties
% 2.89/1.06  
% 2.89/1.06  clauses:                                42
% 2.89/1.06  conjectures:                            13
% 2.89/1.06  epr:                                    10
% 2.89/1.06  horn:                                   35
% 2.89/1.06  ground:                                 13
% 2.89/1.06  unary:                                  12
% 2.89/1.06  binary:                                 11
% 2.89/1.06  lits:                                   144
% 2.89/1.06  lits_eq:                                2
% 2.89/1.06  fd_pure:                                0
% 2.89/1.06  fd_pseudo:                              0
% 2.89/1.06  fd_cond:                                0
% 2.89/1.06  fd_pseudo_cond:                         1
% 2.89/1.06  ac_symbols:                             0
% 2.89/1.06  
% 2.89/1.06  ------ Propositional Solver
% 2.89/1.06  
% 2.89/1.06  prop_solver_calls:                      28
% 2.89/1.06  prop_fast_solver_calls:                 2126
% 2.89/1.06  smt_solver_calls:                       0
% 2.89/1.06  smt_fast_solver_calls:                  0
% 2.89/1.06  prop_num_of_clauses:                    2091
% 2.89/1.06  prop_preprocess_simplified:             8428
% 2.89/1.06  prop_fo_subsumed:                       30
% 2.89/1.06  prop_solver_time:                       0.
% 2.89/1.06  smt_solver_time:                        0.
% 2.89/1.06  smt_fast_solver_time:                   0.
% 2.89/1.06  prop_fast_solver_time:                  0.
% 2.89/1.06  prop_unsat_core_time:                   0.
% 2.89/1.06  
% 2.89/1.06  ------ QBF
% 2.89/1.06  
% 2.89/1.06  qbf_q_res:                              0
% 2.89/1.06  qbf_num_tautologies:                    0
% 2.89/1.06  qbf_prep_cycles:                        0
% 2.89/1.06  
% 2.89/1.06  ------ BMC1
% 2.89/1.06  
% 2.89/1.06  bmc1_current_bound:                     -1
% 2.89/1.06  bmc1_last_solved_bound:                 -1
% 2.89/1.06  bmc1_unsat_core_size:                   -1
% 2.89/1.06  bmc1_unsat_core_parents_size:           -1
% 2.89/1.06  bmc1_merge_next_fun:                    0
% 2.89/1.06  bmc1_unsat_core_clauses_time:           0.
% 2.89/1.06  
% 2.89/1.06  ------ Instantiation
% 2.89/1.06  
% 2.89/1.06  inst_num_of_clauses:                    573
% 2.89/1.06  inst_num_in_passive:                    88
% 2.89/1.06  inst_num_in_active:                     412
% 2.89/1.06  inst_num_in_unprocessed:                73
% 2.89/1.06  inst_num_of_loops:                      440
% 2.89/1.06  inst_num_of_learning_restarts:          0
% 2.89/1.06  inst_num_moves_active_passive:          25
% 2.89/1.06  inst_lit_activity:                      0
% 2.89/1.06  inst_lit_activity_moves:                0
% 2.89/1.06  inst_num_tautologies:                   0
% 2.89/1.06  inst_num_prop_implied:                  0
% 2.89/1.06  inst_num_existing_simplified:           0
% 2.89/1.06  inst_num_eq_res_simplified:             0
% 2.89/1.06  inst_num_child_elim:                    0
% 2.89/1.06  inst_num_of_dismatching_blockings:      340
% 2.89/1.06  inst_num_of_non_proper_insts:           987
% 2.89/1.06  inst_num_of_duplicates:                 0
% 2.89/1.06  inst_inst_num_from_inst_to_res:         0
% 2.89/1.06  inst_dismatching_checking_time:         0.
% 2.89/1.06  
% 2.89/1.06  ------ Resolution
% 2.89/1.06  
% 2.89/1.06  res_num_of_clauses:                     0
% 2.89/1.06  res_num_in_passive:                     0
% 2.89/1.06  res_num_in_active:                      0
% 2.89/1.06  res_num_of_loops:                       209
% 2.89/1.06  res_forward_subset_subsumed:            152
% 2.89/1.06  res_backward_subset_subsumed:           4
% 2.89/1.06  res_forward_subsumed:                   0
% 2.89/1.06  res_backward_subsumed:                  0
% 2.89/1.06  res_forward_subsumption_resolution:     0
% 2.89/1.06  res_backward_subsumption_resolution:    0
% 2.89/1.06  res_clause_to_clause_subsumption:       626
% 2.89/1.06  res_orphan_elimination:                 0
% 2.89/1.06  res_tautology_del:                      114
% 2.89/1.06  res_num_eq_res_simplified:              0
% 2.89/1.06  res_num_sel_changes:                    0
% 2.89/1.06  res_moves_from_active_to_pass:          0
% 2.89/1.06  
% 2.89/1.06  ------ Superposition
% 2.89/1.06  
% 2.89/1.06  sup_time_total:                         0.
% 2.89/1.06  sup_time_generating:                    0.
% 2.89/1.06  sup_time_sim_full:                      0.
% 2.89/1.06  sup_time_sim_immed:                     0.
% 2.89/1.06  
% 2.89/1.06  sup_num_of_clauses:                     164
% 2.89/1.06  sup_num_in_active:                      70
% 2.89/1.06  sup_num_in_passive:                     94
% 2.89/1.06  sup_num_of_loops:                       87
% 2.89/1.06  sup_fw_superposition:                   70
% 2.89/1.06  sup_bw_superposition:                   98
% 2.89/1.06  sup_immediate_simplified:               47
% 2.89/1.06  sup_given_eliminated:                   0
% 2.89/1.06  comparisons_done:                       0
% 2.89/1.06  comparisons_avoided:                    0
% 2.89/1.06  
% 2.89/1.06  ------ Simplifications
% 2.89/1.06  
% 2.89/1.06  
% 2.89/1.06  sim_fw_subset_subsumed:                 4
% 2.89/1.06  sim_bw_subset_subsumed:                 4
% 2.89/1.06  sim_fw_subsumed:                        9
% 2.89/1.06  sim_bw_subsumed:                        0
% 2.89/1.06  sim_fw_subsumption_res:                 8
% 2.89/1.06  sim_bw_subsumption_res:                 0
% 2.89/1.06  sim_tautology_del:                      13
% 2.89/1.06  sim_eq_tautology_del:                   1
% 2.89/1.06  sim_eq_res_simp:                        0
% 2.89/1.06  sim_fw_demodulated:                     0
% 2.89/1.06  sim_bw_demodulated:                     14
% 2.89/1.06  sim_light_normalised:                   35
% 2.89/1.06  sim_joinable_taut:                      0
% 2.89/1.06  sim_joinable_simp:                      0
% 2.89/1.06  sim_ac_normalised:                      0
% 2.89/1.06  sim_smt_subsumption:                    0
% 2.89/1.06  
%------------------------------------------------------------------------------
