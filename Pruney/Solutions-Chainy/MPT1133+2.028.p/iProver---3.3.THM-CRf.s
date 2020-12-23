%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:54 EST 2020

% Result     : Theorem 15.24s
% Output     : CNFRefutation 15.24s
% Verified   : 
% Statistics : Number of formulae       :  325 (245474 expanded)
%              Number of clauses        :  227 (58476 expanded)
%              Number of leaves         :   28 (70528 expanded)
%              Depth                    :   34
%              Number of atoms          : 1426 (2599125 expanded)
%              Number of equality atoms :  630 (308277 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

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
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f68,plain,(
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
     => ( ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK6 = X2
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
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
              | ~ v5_pre_topc(sK5,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK5,X0,X1) )
            & sK5 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
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
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
                  | ~ v5_pre_topc(X2,X0,sK4) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
                  | v5_pre_topc(X2,X0,sK4) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK4)
        & v2_pre_topc(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK3,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
      | ~ v5_pre_topc(sK5,sK3,sK4) )
    & ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
      | v5_pre_topc(sK5,sK3,sK4) )
    & sK5 = sK6
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f64,f68,f67,f66,f65])).

fof(f110,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f69])).

fof(f114,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f69])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f111,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f69])).

fof(f109,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f69])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f55])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f117,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f79])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f118,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f113,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    inference(cnf_transformation,[],[f69])).

fof(f112,plain,(
    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(cnf_transformation,[],[f69])).

fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f103,plain,(
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
    inference(cnf_transformation,[],[f62])).

fof(f123,plain,(
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
    inference(equality_resolution,[],[f103])).

fof(f104,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f105,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f106,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f107,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f115,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f99,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f97,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,(
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
    inference(cnf_transformation,[],[f62])).

fof(f124,plain,(
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
    inference(equality_resolution,[],[f102])).

fof(f116,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f101,plain,(
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
    inference(cnf_transformation,[],[f61])).

fof(f121,plain,(
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
    inference(equality_resolution,[],[f101])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f61])).

fof(f122,plain,(
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
    inference(equality_resolution,[],[f100])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK2(X0,X1),X0,X1)
        & v1_funct_1(sK2(X0,X1))
        & v4_relat_1(sK2(X0,X1),X0)
        & v1_relat_1(sK2(X0,X1))
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK2(X0,X1),X0,X1)
      & v1_funct_1(sK2(X0,X1))
      & v4_relat_1(sK2(X0,X1),X0)
      & v1_relat_1(sK2(X0,X1))
      & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f59])).

fof(f94,plain,(
    ! [X0,X1] : v1_funct_2(sK2(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f60])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f120,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f96])).

fof(f90,plain,(
    ! [X0,X1] : m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_3461,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_36,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3491,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3461,c_36])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_19,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_715,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_26,c_19])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_719,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_715,c_16,c_15])).

cnf(c_720,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_719])).

cnf(c_3453,plain,
    ( k1_relat_1(X0) = X1
    | k1_xboole_0 = X2
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_3774,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3491,c_3453])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3460,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_3490,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3460,c_36])).

cnf(c_3532,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3490])).

cnf(c_3775,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK6)
    | u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3774])).

cnf(c_4101,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3774,c_39,c_3532,c_3775])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3477,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6974,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3491,c_3477])).

cnf(c_7014,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4101,c_6974])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_132,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4107,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4101,c_3491])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_4109,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4107,c_7])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_6979,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_3477])).

cnf(c_7001,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4109,c_6979])).

cnf(c_7009,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7001])).

cnf(c_7127,plain,
    ( v1_xboole_0(sK6) = iProver_top
    | u1_struct_0(sK3) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7014,c_132,c_7009])).

cnf(c_7128,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_xboole_0(sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_7127])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3481,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7131,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7128,c_3481])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3464,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_22315,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7131,c_3464])).

cnf(c_23158,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | sK6 = k1_xboole_0
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_22315,c_3453])).

cnf(c_54,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3762,plain,
    ( ~ v1_xboole_0(sK6)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2611,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4121,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_2611])).

cnf(c_2612,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3787,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_4254,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3787])).

cnf(c_4255,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_4254])).

cnf(c_6972,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3464,c_3477])).

cnf(c_6984,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v1_xboole_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6972])).

cnf(c_2613,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_9824,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X0 ),
    inference(instantiation,[status(thm)],[c_2613])).

cnf(c_9826,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9824])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_3463,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_22316,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7131,c_3463])).

cnf(c_23383,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23158,c_54,c_5,c_3762,c_4121,c_4255,c_6984,c_9826,c_22316])).

cnf(c_32,plain,
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
    inference(cnf_transformation,[],[f123])).

cnf(c_3468,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4831,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3464,c_3468])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_47,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_48,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_49,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_50,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_55,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_35,negated_conjecture,
    ( v5_pre_topc(sK5,sK3,sK4)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3465,plain,
    ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3492,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3465,c_36])).

cnf(c_29,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3604,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3605,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3604])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3687,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3688,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3687])).

cnf(c_28,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3794,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_3795,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3794])).

cnf(c_33,plain,
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
    inference(cnf_transformation,[],[f124])).

cnf(c_3467,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4309,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3464,c_3467])).

cnf(c_34,negated_conjecture,
    ( ~ v5_pre_topc(sK5,sK3,sK4)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3466,plain,
    ( v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3493,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,sK3,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3466,c_36])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f121])).

cnf(c_3712,plain,
    ( v5_pre_topc(sK6,X0,sK4)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3928,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK6,sK3,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3712])).

cnf(c_3929,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3928])).

cnf(c_4414,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4309,c_47,c_48,c_49,c_50,c_54,c_55,c_3493,c_3491,c_3490,c_3605,c_3688,c_3795,c_3929])).

cnf(c_4415,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4414])).

cnf(c_31,plain,
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
    inference(cnf_transformation,[],[f122])).

cnf(c_3893,plain,
    ( ~ v5_pre_topc(sK6,X0,sK4)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_4472,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v5_pre_topc(sK6,sK3,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3893])).

cnf(c_4473,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) = iProver_top
    | v5_pre_topc(sK6,sK3,sK4) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4472])).

cnf(c_4941,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4831,c_47,c_48,c_49,c_50,c_54,c_55,c_3492,c_3491,c_3490,c_3605,c_3688,c_3795,c_4415,c_4473])).

cnf(c_4942,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4941])).

cnf(c_22306,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7131,c_4942])).

cnf(c_23504,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_23383,c_22306])).

cnf(c_23506,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_23383,c_22316])).

cnf(c_23505,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_23383,c_22315])).

cnf(c_3469,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5385,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3464,c_3469])).

cnf(c_56,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3619,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3620,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3619])).

cnf(c_3697,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3698,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3697])).

cnf(c_3822,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_3823,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3822])).

cnf(c_3713,plain,
    ( ~ v5_pre_topc(sK6,X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK6,X0,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_3902,plain,
    ( ~ v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK6,sK3,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3713])).

cnf(c_3903,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3902])).

cnf(c_3965,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3969,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3965])).

cnf(c_3971,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(sK6,sK3,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_3972,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,sK3,sK4) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3971])).

cnf(c_5969,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5385,c_47,c_48,c_49,c_50,c_54,c_55,c_56,c_3493,c_3492,c_3491,c_3490,c_3620,c_3698,c_3823,c_3903,c_3969,c_3972])).

cnf(c_5970,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5969])).

cnf(c_5973,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5970,c_47,c_48,c_49,c_50,c_54,c_55,c_56,c_3492,c_3491,c_3490,c_3620,c_3698,c_3823,c_3969,c_3972])).

cnf(c_22301,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7131,c_5973])).

cnf(c_23848,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_23505,c_22301])).

cnf(c_28791,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7131,c_23848])).

cnf(c_28859,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23504,c_23506,c_28791])).

cnf(c_29130,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_28859,c_4101])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3479,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3470,plain,
    ( v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6599,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),X1) != iProver_top
    | v5_pre_topc(X0,sK4,X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4101,c_3470])).

cnf(c_7543,plain,
    ( l1_pre_topc(X1) != iProver_top
    | u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),X1) != iProver_top
    | v5_pre_topc(X0,sK4,X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6599,c_49,c_50])).

cnf(c_7544,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),X1) != iProver_top
    | v5_pre_topc(X0,sK4,X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7543])).

cnf(c_7549,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),X1) != iProver_top
    | v5_pre_topc(X0,sK4,X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))),u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3479,c_7544])).

cnf(c_48122,plain,
    ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),X1) != iProver_top
    | v5_pre_topc(X0,sK4,X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))),u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7549,c_28859])).

cnf(c_48129,plain,
    ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK4) != iProver_top
    | v5_pre_topc(X0,sK4,sK4) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_xboole_0) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))),u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_29130,c_48122])).

cnf(c_20,plain,
    ( v1_funct_2(sK2(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_99,plain,
    ( v1_funct_2(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_98,plain,
    ( v1_funct_2(sK2(X0,X1),X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_100,plain,
    ( v1_funct_2(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_127,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_128,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_11,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3480,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3489,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3480,c_10])).

cnf(c_3513,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3489])).

cnf(c_3515,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3513])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_743,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ v4_relat_1(X2,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X2)
    | X0 != X2
    | k1_relat_1(X2) = X3
    | k1_xboole_0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_744,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ v4_relat_1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_760,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_744,c_15,c_16])).

cnf(c_3452,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_760])).

cnf(c_3494,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3452,c_8])).

cnf(c_3521,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3494])).

cnf(c_3523,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3521])).

cnf(c_3673,plain,
    ( X0 != X1
    | X0 = sK6
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_3674,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3673])).

cnf(c_2619,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4806,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK6)
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2619])).

cnf(c_4808,plain,
    ( ~ v1_funct_1(sK6)
    | v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_4806])).

cnf(c_2618,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_6675,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK2(X3,X4),X3,X4)
    | X1 != X3
    | X2 != X4
    | X0 != sK2(X3,X4) ),
    inference(instantiation,[status(thm)],[c_2618])).

cnf(c_6677,plain,
    ( ~ v1_funct_2(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK2(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6675])).

cnf(c_6676,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != sK2(X1,X3)
    | v1_funct_2(X4,X0,X2) = iProver_top
    | v1_funct_2(sK2(X1,X3),X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6675])).

cnf(c_6678,plain,
    ( k1_xboole_0 != sK2(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6676])).

cnf(c_24,plain,
    ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3474,plain,
    ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6971,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3474,c_3477])).

cnf(c_6981,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2(X1,X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6971])).

cnf(c_6983,plain,
    ( v1_xboole_0(sK2(k1_xboole_0,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6981])).

cnf(c_3996,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3464,c_3453])).

cnf(c_3997,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3996])).

cnf(c_4619,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3996,c_39,c_38,c_3997])).

cnf(c_4626,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4619,c_3463])).

cnf(c_4621,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_4101,c_4619])).

cnf(c_5065,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4621,c_4942])).

cnf(c_4945,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4101,c_4942])).

cnf(c_4946,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4945,c_7])).

cnf(c_5260,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | u1_struct_0(sK3) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5065,c_4109,c_4946])).

cnf(c_5261,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5260])).

cnf(c_5265,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4101,c_5261])).

cnf(c_5380,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | u1_struct_0(sK3) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_4626,c_5265])).

cnf(c_6211,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5380,c_5261])).

cnf(c_29006,plain,
    ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28859,c_6211])).

cnf(c_31675,plain,
    ( ~ v1_xboole_0(sK2(X0,X1))
    | k1_xboole_0 = sK2(X0,X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_31677,plain,
    ( ~ v1_xboole_0(sK2(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = sK2(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_31675])).

cnf(c_48295,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,k1_relat_1(X4),u1_struct_0(sK4))
    | X3 != X0
    | u1_struct_0(sK4) != X2
    | k1_relat_1(X4) != X1 ),
    inference(instantiation,[status(thm)],[c_2618])).

cnf(c_48297,plain,
    ( X0 != X1
    | u1_struct_0(sK4) != X2
    | k1_relat_1(X3) != X4
    | v1_funct_2(X1,X4,X2) != iProver_top
    | v1_funct_2(X0,k1_relat_1(X3),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48295])).

cnf(c_48299,plain,
    ( u1_struct_0(sK4) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK4)) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_48297])).

cnf(c_48311,plain,
    ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_48129,c_39,c_99,c_100,c_127,c_128,c_5,c_3515,c_3523,c_3674,c_4808,c_6677,c_6678,c_6983,c_23506,c_28791,c_29006,c_29130,c_31677,c_48299])).

cnf(c_29133,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_28859,c_3464])).

cnf(c_48351,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_48311,c_29133])).

cnf(c_29124,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_28859,c_4619])).

cnf(c_6643,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3479,c_3469])).

cnf(c_44485,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),X1) = iProver_top
    | v5_pre_topc(X0,sK4,X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_29124,c_6643])).

cnf(c_44494,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),X1) = iProver_top
    | v5_pre_topc(X0,sK4,X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_44485,c_8])).

cnf(c_6646,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3479,c_5973])).

cnf(c_6731,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4619,c_6646])).

cnf(c_6733,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | r1_tarski(sK6,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6731,c_7])).

cnf(c_4625,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4619,c_3464])).

cnf(c_4627,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4625,c_7])).

cnf(c_5977,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4619,c_5973])).

cnf(c_5979,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5977,c_7])).

cnf(c_7247,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6733,c_4627,c_5979])).

cnf(c_7248,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7247])).

cnf(c_29095,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28859,c_7248])).

cnf(c_44900,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | X3 != X0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X2
    | u1_struct_0(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_2618])).

cnf(c_44902,plain,
    ( X0 != X1
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X2
    | u1_struct_0(sK3) != X3
    | v1_funct_2(X1,X3,X2) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44900])).

cnf(c_44904,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_xboole_0
    | u1_struct_0(sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_44902])).

cnf(c_44597,plain,
    ( X0 != X1
    | u1_struct_0(sK3) != X1
    | u1_struct_0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_46911,plain,
    ( X0 != k1_relat_1(X1)
    | u1_struct_0(sK3) = X0
    | u1_struct_0(sK3) != k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_44597])).

cnf(c_46917,plain,
    ( u1_struct_0(sK3) != k1_relat_1(k1_xboole_0)
    | u1_struct_0(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_46911])).

cnf(c_48276,plain,
    ( X0 != X1
    | X0 = k1_relat_1(X2)
    | k1_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_48278,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_48276])).

cnf(c_48678,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_44494,c_39,c_99,c_100,c_127,c_128,c_5,c_3515,c_3523,c_3674,c_4808,c_6677,c_6678,c_6983,c_23506,c_28791,c_29006,c_29095,c_29124,c_29130,c_31677,c_44904,c_46917,c_48278,c_48299])).

cnf(c_48680,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_48678,c_48311])).

cnf(c_49062,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_48351,c_48680])).

cnf(c_29134,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_28859,c_3463])).

cnf(c_48352,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_48311,c_29134])).

cnf(c_48963,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_48352,c_48680])).

cnf(c_29115,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28859,c_5973])).

cnf(c_48344,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_48311,c_29115])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_49062,c_48963,c_48344])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.24/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.24/2.50  
% 15.24/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.24/2.50  
% 15.24/2.50  ------  iProver source info
% 15.24/2.50  
% 15.24/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.24/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.24/2.50  git: non_committed_changes: false
% 15.24/2.50  git: last_make_outside_of_git: false
% 15.24/2.50  
% 15.24/2.50  ------ 
% 15.24/2.50  
% 15.24/2.50  ------ Input Options
% 15.24/2.50  
% 15.24/2.50  --out_options                           all
% 15.24/2.50  --tptp_safe_out                         true
% 15.24/2.50  --problem_path                          ""
% 15.24/2.50  --include_path                          ""
% 15.24/2.50  --clausifier                            res/vclausify_rel
% 15.24/2.50  --clausifier_options                    ""
% 15.24/2.50  --stdin                                 false
% 15.24/2.50  --stats_out                             all
% 15.24/2.50  
% 15.24/2.50  ------ General Options
% 15.24/2.50  
% 15.24/2.50  --fof                                   false
% 15.24/2.50  --time_out_real                         305.
% 15.24/2.50  --time_out_virtual                      -1.
% 15.24/2.50  --symbol_type_check                     false
% 15.24/2.50  --clausify_out                          false
% 15.24/2.50  --sig_cnt_out                           false
% 15.24/2.50  --trig_cnt_out                          false
% 15.24/2.50  --trig_cnt_out_tolerance                1.
% 15.24/2.50  --trig_cnt_out_sk_spl                   false
% 15.24/2.50  --abstr_cl_out                          false
% 15.24/2.50  
% 15.24/2.50  ------ Global Options
% 15.24/2.50  
% 15.24/2.50  --schedule                              default
% 15.24/2.50  --add_important_lit                     false
% 15.24/2.50  --prop_solver_per_cl                    1000
% 15.24/2.50  --min_unsat_core                        false
% 15.24/2.50  --soft_assumptions                      false
% 15.24/2.50  --soft_lemma_size                       3
% 15.24/2.50  --prop_impl_unit_size                   0
% 15.24/2.50  --prop_impl_unit                        []
% 15.24/2.50  --share_sel_clauses                     true
% 15.24/2.50  --reset_solvers                         false
% 15.24/2.50  --bc_imp_inh                            [conj_cone]
% 15.24/2.50  --conj_cone_tolerance                   3.
% 15.24/2.50  --extra_neg_conj                        none
% 15.24/2.50  --large_theory_mode                     true
% 15.24/2.50  --prolific_symb_bound                   200
% 15.24/2.50  --lt_threshold                          2000
% 15.24/2.50  --clause_weak_htbl                      true
% 15.24/2.50  --gc_record_bc_elim                     false
% 15.24/2.50  
% 15.24/2.50  ------ Preprocessing Options
% 15.24/2.50  
% 15.24/2.50  --preprocessing_flag                    true
% 15.24/2.50  --time_out_prep_mult                    0.1
% 15.24/2.50  --splitting_mode                        input
% 15.24/2.50  --splitting_grd                         true
% 15.24/2.50  --splitting_cvd                         false
% 15.24/2.50  --splitting_cvd_svl                     false
% 15.24/2.50  --splitting_nvd                         32
% 15.24/2.50  --sub_typing                            true
% 15.24/2.50  --prep_gs_sim                           true
% 15.24/2.50  --prep_unflatten                        true
% 15.24/2.50  --prep_res_sim                          true
% 15.24/2.50  --prep_upred                            true
% 15.24/2.50  --prep_sem_filter                       exhaustive
% 15.24/2.50  --prep_sem_filter_out                   false
% 15.24/2.50  --pred_elim                             true
% 15.24/2.50  --res_sim_input                         true
% 15.24/2.50  --eq_ax_congr_red                       true
% 15.24/2.50  --pure_diseq_elim                       true
% 15.24/2.50  --brand_transform                       false
% 15.24/2.50  --non_eq_to_eq                          false
% 15.24/2.50  --prep_def_merge                        true
% 15.24/2.50  --prep_def_merge_prop_impl              false
% 15.24/2.50  --prep_def_merge_mbd                    true
% 15.24/2.50  --prep_def_merge_tr_red                 false
% 15.24/2.50  --prep_def_merge_tr_cl                  false
% 15.24/2.50  --smt_preprocessing                     true
% 15.24/2.50  --smt_ac_axioms                         fast
% 15.24/2.50  --preprocessed_out                      false
% 15.24/2.50  --preprocessed_stats                    false
% 15.24/2.50  
% 15.24/2.50  ------ Abstraction refinement Options
% 15.24/2.50  
% 15.24/2.50  --abstr_ref                             []
% 15.24/2.50  --abstr_ref_prep                        false
% 15.24/2.50  --abstr_ref_until_sat                   false
% 15.24/2.50  --abstr_ref_sig_restrict                funpre
% 15.24/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.24/2.50  --abstr_ref_under                       []
% 15.24/2.50  
% 15.24/2.50  ------ SAT Options
% 15.24/2.50  
% 15.24/2.50  --sat_mode                              false
% 15.24/2.50  --sat_fm_restart_options                ""
% 15.24/2.50  --sat_gr_def                            false
% 15.24/2.50  --sat_epr_types                         true
% 15.24/2.50  --sat_non_cyclic_types                  false
% 15.24/2.50  --sat_finite_models                     false
% 15.24/2.50  --sat_fm_lemmas                         false
% 15.24/2.50  --sat_fm_prep                           false
% 15.24/2.50  --sat_fm_uc_incr                        true
% 15.24/2.50  --sat_out_model                         small
% 15.24/2.50  --sat_out_clauses                       false
% 15.24/2.50  
% 15.24/2.50  ------ QBF Options
% 15.24/2.50  
% 15.24/2.50  --qbf_mode                              false
% 15.24/2.50  --qbf_elim_univ                         false
% 15.24/2.50  --qbf_dom_inst                          none
% 15.24/2.50  --qbf_dom_pre_inst                      false
% 15.24/2.50  --qbf_sk_in                             false
% 15.24/2.50  --qbf_pred_elim                         true
% 15.24/2.50  --qbf_split                             512
% 15.24/2.50  
% 15.24/2.50  ------ BMC1 Options
% 15.24/2.50  
% 15.24/2.50  --bmc1_incremental                      false
% 15.24/2.50  --bmc1_axioms                           reachable_all
% 15.24/2.50  --bmc1_min_bound                        0
% 15.24/2.50  --bmc1_max_bound                        -1
% 15.24/2.50  --bmc1_max_bound_default                -1
% 15.24/2.50  --bmc1_symbol_reachability              true
% 15.24/2.50  --bmc1_property_lemmas                  false
% 15.24/2.50  --bmc1_k_induction                      false
% 15.24/2.50  --bmc1_non_equiv_states                 false
% 15.24/2.50  --bmc1_deadlock                         false
% 15.24/2.50  --bmc1_ucm                              false
% 15.24/2.50  --bmc1_add_unsat_core                   none
% 15.24/2.50  --bmc1_unsat_core_children              false
% 15.24/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.24/2.50  --bmc1_out_stat                         full
% 15.24/2.50  --bmc1_ground_init                      false
% 15.24/2.50  --bmc1_pre_inst_next_state              false
% 15.24/2.50  --bmc1_pre_inst_state                   false
% 15.24/2.50  --bmc1_pre_inst_reach_state             false
% 15.24/2.50  --bmc1_out_unsat_core                   false
% 15.24/2.50  --bmc1_aig_witness_out                  false
% 15.24/2.50  --bmc1_verbose                          false
% 15.24/2.50  --bmc1_dump_clauses_tptp                false
% 15.24/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.24/2.50  --bmc1_dump_file                        -
% 15.24/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.24/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.24/2.50  --bmc1_ucm_extend_mode                  1
% 15.24/2.50  --bmc1_ucm_init_mode                    2
% 15.24/2.50  --bmc1_ucm_cone_mode                    none
% 15.24/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.24/2.50  --bmc1_ucm_relax_model                  4
% 15.24/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.24/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.24/2.50  --bmc1_ucm_layered_model                none
% 15.24/2.50  --bmc1_ucm_max_lemma_size               10
% 15.24/2.50  
% 15.24/2.50  ------ AIG Options
% 15.24/2.50  
% 15.24/2.50  --aig_mode                              false
% 15.24/2.50  
% 15.24/2.50  ------ Instantiation Options
% 15.24/2.50  
% 15.24/2.50  --instantiation_flag                    true
% 15.24/2.50  --inst_sos_flag                         true
% 15.24/2.50  --inst_sos_phase                        true
% 15.24/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.24/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.24/2.50  --inst_lit_sel_side                     num_symb
% 15.24/2.50  --inst_solver_per_active                1400
% 15.24/2.50  --inst_solver_calls_frac                1.
% 15.24/2.50  --inst_passive_queue_type               priority_queues
% 15.24/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.24/2.50  --inst_passive_queues_freq              [25;2]
% 15.24/2.50  --inst_dismatching                      true
% 15.24/2.50  --inst_eager_unprocessed_to_passive     true
% 15.24/2.50  --inst_prop_sim_given                   true
% 15.24/2.50  --inst_prop_sim_new                     false
% 15.24/2.50  --inst_subs_new                         false
% 15.24/2.50  --inst_eq_res_simp                      false
% 15.24/2.50  --inst_subs_given                       false
% 15.24/2.50  --inst_orphan_elimination               true
% 15.24/2.50  --inst_learning_loop_flag               true
% 15.24/2.50  --inst_learning_start                   3000
% 15.24/2.50  --inst_learning_factor                  2
% 15.24/2.50  --inst_start_prop_sim_after_learn       3
% 15.24/2.50  --inst_sel_renew                        solver
% 15.24/2.50  --inst_lit_activity_flag                true
% 15.24/2.50  --inst_restr_to_given                   false
% 15.24/2.50  --inst_activity_threshold               500
% 15.24/2.50  --inst_out_proof                        true
% 15.24/2.50  
% 15.24/2.50  ------ Resolution Options
% 15.24/2.50  
% 15.24/2.50  --resolution_flag                       true
% 15.24/2.50  --res_lit_sel                           adaptive
% 15.24/2.50  --res_lit_sel_side                      none
% 15.24/2.50  --res_ordering                          kbo
% 15.24/2.50  --res_to_prop_solver                    active
% 15.24/2.50  --res_prop_simpl_new                    false
% 15.24/2.50  --res_prop_simpl_given                  true
% 15.24/2.50  --res_passive_queue_type                priority_queues
% 15.24/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.24/2.50  --res_passive_queues_freq               [15;5]
% 15.24/2.50  --res_forward_subs                      full
% 15.24/2.50  --res_backward_subs                     full
% 15.24/2.50  --res_forward_subs_resolution           true
% 15.24/2.50  --res_backward_subs_resolution          true
% 15.24/2.50  --res_orphan_elimination                true
% 15.24/2.50  --res_time_limit                        2.
% 15.24/2.50  --res_out_proof                         true
% 15.24/2.50  
% 15.24/2.50  ------ Superposition Options
% 15.24/2.50  
% 15.24/2.50  --superposition_flag                    true
% 15.24/2.50  --sup_passive_queue_type                priority_queues
% 15.24/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.24/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.24/2.50  --demod_completeness_check              fast
% 15.24/2.50  --demod_use_ground                      true
% 15.24/2.50  --sup_to_prop_solver                    passive
% 15.24/2.50  --sup_prop_simpl_new                    true
% 15.24/2.50  --sup_prop_simpl_given                  true
% 15.24/2.50  --sup_fun_splitting                     true
% 15.24/2.50  --sup_smt_interval                      50000
% 15.24/2.50  
% 15.24/2.50  ------ Superposition Simplification Setup
% 15.24/2.50  
% 15.24/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.24/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.24/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.24/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.24/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.24/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.24/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.24/2.50  --sup_immed_triv                        [TrivRules]
% 15.24/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.50  --sup_immed_bw_main                     []
% 15.24/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.24/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.24/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.50  --sup_input_bw                          []
% 15.24/2.50  
% 15.24/2.50  ------ Combination Options
% 15.24/2.50  
% 15.24/2.50  --comb_res_mult                         3
% 15.24/2.50  --comb_sup_mult                         2
% 15.24/2.50  --comb_inst_mult                        10
% 15.24/2.50  
% 15.24/2.50  ------ Debug Options
% 15.24/2.50  
% 15.24/2.50  --dbg_backtrace                         false
% 15.24/2.50  --dbg_dump_prop_clauses                 false
% 15.24/2.50  --dbg_dump_prop_clauses_file            -
% 15.24/2.50  --dbg_out_stat                          false
% 15.24/2.50  ------ Parsing...
% 15.24/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.24/2.50  
% 15.24/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 15.24/2.50  
% 15.24/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.24/2.50  
% 15.24/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.24/2.50  ------ Proving...
% 15.24/2.50  ------ Problem Properties 
% 15.24/2.50  
% 15.24/2.50  
% 15.24/2.50  clauses                                 41
% 15.24/2.50  conjectures                             13
% 15.24/2.50  EPR                                     12
% 15.24/2.50  Horn                                    36
% 15.24/2.50  unary                                   19
% 15.24/2.50  binary                                  11
% 15.24/2.50  lits                                    109
% 15.24/2.50  lits eq                                 11
% 15.24/2.50  fd_pure                                 0
% 15.24/2.50  fd_pseudo                               0
% 15.24/2.50  fd_cond                                 2
% 15.24/2.50  fd_pseudo_cond                          1
% 15.24/2.50  AC symbols                              0
% 15.24/2.50  
% 15.24/2.50  ------ Schedule dynamic 5 is on 
% 15.24/2.50  
% 15.24/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.24/2.50  
% 15.24/2.50  
% 15.24/2.50  ------ 
% 15.24/2.50  Current options:
% 15.24/2.50  ------ 
% 15.24/2.50  
% 15.24/2.50  ------ Input Options
% 15.24/2.50  
% 15.24/2.50  --out_options                           all
% 15.24/2.50  --tptp_safe_out                         true
% 15.24/2.50  --problem_path                          ""
% 15.24/2.50  --include_path                          ""
% 15.24/2.50  --clausifier                            res/vclausify_rel
% 15.24/2.50  --clausifier_options                    ""
% 15.24/2.50  --stdin                                 false
% 15.24/2.50  --stats_out                             all
% 15.24/2.50  
% 15.24/2.50  ------ General Options
% 15.24/2.50  
% 15.24/2.50  --fof                                   false
% 15.24/2.50  --time_out_real                         305.
% 15.24/2.50  --time_out_virtual                      -1.
% 15.24/2.50  --symbol_type_check                     false
% 15.24/2.50  --clausify_out                          false
% 15.24/2.50  --sig_cnt_out                           false
% 15.24/2.50  --trig_cnt_out                          false
% 15.24/2.50  --trig_cnt_out_tolerance                1.
% 15.24/2.50  --trig_cnt_out_sk_spl                   false
% 15.24/2.50  --abstr_cl_out                          false
% 15.24/2.50  
% 15.24/2.50  ------ Global Options
% 15.24/2.50  
% 15.24/2.50  --schedule                              default
% 15.24/2.50  --add_important_lit                     false
% 15.24/2.50  --prop_solver_per_cl                    1000
% 15.24/2.50  --min_unsat_core                        false
% 15.24/2.50  --soft_assumptions                      false
% 15.24/2.50  --soft_lemma_size                       3
% 15.24/2.50  --prop_impl_unit_size                   0
% 15.24/2.50  --prop_impl_unit                        []
% 15.24/2.50  --share_sel_clauses                     true
% 15.24/2.50  --reset_solvers                         false
% 15.24/2.50  --bc_imp_inh                            [conj_cone]
% 15.24/2.50  --conj_cone_tolerance                   3.
% 15.24/2.50  --extra_neg_conj                        none
% 15.24/2.50  --large_theory_mode                     true
% 15.24/2.50  --prolific_symb_bound                   200
% 15.24/2.50  --lt_threshold                          2000
% 15.24/2.50  --clause_weak_htbl                      true
% 15.24/2.50  --gc_record_bc_elim                     false
% 15.24/2.50  
% 15.24/2.50  ------ Preprocessing Options
% 15.24/2.50  
% 15.24/2.50  --preprocessing_flag                    true
% 15.24/2.50  --time_out_prep_mult                    0.1
% 15.24/2.50  --splitting_mode                        input
% 15.24/2.50  --splitting_grd                         true
% 15.24/2.50  --splitting_cvd                         false
% 15.24/2.50  --splitting_cvd_svl                     false
% 15.24/2.50  --splitting_nvd                         32
% 15.24/2.50  --sub_typing                            true
% 15.24/2.50  --prep_gs_sim                           true
% 15.24/2.50  --prep_unflatten                        true
% 15.24/2.50  --prep_res_sim                          true
% 15.24/2.50  --prep_upred                            true
% 15.24/2.50  --prep_sem_filter                       exhaustive
% 15.24/2.50  --prep_sem_filter_out                   false
% 15.24/2.50  --pred_elim                             true
% 15.24/2.50  --res_sim_input                         true
% 15.24/2.50  --eq_ax_congr_red                       true
% 15.24/2.50  --pure_diseq_elim                       true
% 15.24/2.50  --brand_transform                       false
% 15.24/2.50  --non_eq_to_eq                          false
% 15.24/2.50  --prep_def_merge                        true
% 15.24/2.50  --prep_def_merge_prop_impl              false
% 15.24/2.50  --prep_def_merge_mbd                    true
% 15.24/2.50  --prep_def_merge_tr_red                 false
% 15.24/2.50  --prep_def_merge_tr_cl                  false
% 15.24/2.50  --smt_preprocessing                     true
% 15.24/2.50  --smt_ac_axioms                         fast
% 15.24/2.50  --preprocessed_out                      false
% 15.24/2.50  --preprocessed_stats                    false
% 15.24/2.50  
% 15.24/2.50  ------ Abstraction refinement Options
% 15.24/2.50  
% 15.24/2.50  --abstr_ref                             []
% 15.24/2.50  --abstr_ref_prep                        false
% 15.24/2.50  --abstr_ref_until_sat                   false
% 15.24/2.50  --abstr_ref_sig_restrict                funpre
% 15.24/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.24/2.50  --abstr_ref_under                       []
% 15.24/2.50  
% 15.24/2.50  ------ SAT Options
% 15.24/2.50  
% 15.24/2.50  --sat_mode                              false
% 15.24/2.50  --sat_fm_restart_options                ""
% 15.24/2.50  --sat_gr_def                            false
% 15.24/2.50  --sat_epr_types                         true
% 15.24/2.50  --sat_non_cyclic_types                  false
% 15.24/2.50  --sat_finite_models                     false
% 15.24/2.50  --sat_fm_lemmas                         false
% 15.24/2.50  --sat_fm_prep                           false
% 15.24/2.50  --sat_fm_uc_incr                        true
% 15.24/2.50  --sat_out_model                         small
% 15.24/2.50  --sat_out_clauses                       false
% 15.24/2.50  
% 15.24/2.50  ------ QBF Options
% 15.24/2.50  
% 15.24/2.50  --qbf_mode                              false
% 15.24/2.50  --qbf_elim_univ                         false
% 15.24/2.50  --qbf_dom_inst                          none
% 15.24/2.50  --qbf_dom_pre_inst                      false
% 15.24/2.50  --qbf_sk_in                             false
% 15.24/2.50  --qbf_pred_elim                         true
% 15.24/2.50  --qbf_split                             512
% 15.24/2.50  
% 15.24/2.50  ------ BMC1 Options
% 15.24/2.50  
% 15.24/2.50  --bmc1_incremental                      false
% 15.24/2.50  --bmc1_axioms                           reachable_all
% 15.24/2.50  --bmc1_min_bound                        0
% 15.24/2.50  --bmc1_max_bound                        -1
% 15.24/2.50  --bmc1_max_bound_default                -1
% 15.24/2.50  --bmc1_symbol_reachability              true
% 15.24/2.50  --bmc1_property_lemmas                  false
% 15.24/2.50  --bmc1_k_induction                      false
% 15.24/2.50  --bmc1_non_equiv_states                 false
% 15.24/2.50  --bmc1_deadlock                         false
% 15.24/2.50  --bmc1_ucm                              false
% 15.24/2.50  --bmc1_add_unsat_core                   none
% 15.24/2.50  --bmc1_unsat_core_children              false
% 15.24/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.24/2.50  --bmc1_out_stat                         full
% 15.24/2.50  --bmc1_ground_init                      false
% 15.24/2.50  --bmc1_pre_inst_next_state              false
% 15.24/2.50  --bmc1_pre_inst_state                   false
% 15.24/2.50  --bmc1_pre_inst_reach_state             false
% 15.24/2.50  --bmc1_out_unsat_core                   false
% 15.24/2.50  --bmc1_aig_witness_out                  false
% 15.24/2.50  --bmc1_verbose                          false
% 15.24/2.50  --bmc1_dump_clauses_tptp                false
% 15.24/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.24/2.50  --bmc1_dump_file                        -
% 15.24/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.24/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.24/2.50  --bmc1_ucm_extend_mode                  1
% 15.24/2.50  --bmc1_ucm_init_mode                    2
% 15.24/2.50  --bmc1_ucm_cone_mode                    none
% 15.24/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.24/2.50  --bmc1_ucm_relax_model                  4
% 15.24/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.24/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.24/2.50  --bmc1_ucm_layered_model                none
% 15.24/2.50  --bmc1_ucm_max_lemma_size               10
% 15.24/2.50  
% 15.24/2.50  ------ AIG Options
% 15.24/2.50  
% 15.24/2.50  --aig_mode                              false
% 15.24/2.50  
% 15.24/2.50  ------ Instantiation Options
% 15.24/2.50  
% 15.24/2.50  --instantiation_flag                    true
% 15.24/2.50  --inst_sos_flag                         true
% 15.24/2.50  --inst_sos_phase                        true
% 15.24/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.24/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.24/2.50  --inst_lit_sel_side                     none
% 15.24/2.50  --inst_solver_per_active                1400
% 15.24/2.50  --inst_solver_calls_frac                1.
% 15.24/2.50  --inst_passive_queue_type               priority_queues
% 15.24/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.24/2.50  --inst_passive_queues_freq              [25;2]
% 15.24/2.50  --inst_dismatching                      true
% 15.24/2.50  --inst_eager_unprocessed_to_passive     true
% 15.24/2.50  --inst_prop_sim_given                   true
% 15.24/2.50  --inst_prop_sim_new                     false
% 15.24/2.50  --inst_subs_new                         false
% 15.24/2.50  --inst_eq_res_simp                      false
% 15.24/2.50  --inst_subs_given                       false
% 15.24/2.50  --inst_orphan_elimination               true
% 15.24/2.50  --inst_learning_loop_flag               true
% 15.24/2.50  --inst_learning_start                   3000
% 15.24/2.50  --inst_learning_factor                  2
% 15.24/2.50  --inst_start_prop_sim_after_learn       3
% 15.24/2.50  --inst_sel_renew                        solver
% 15.24/2.50  --inst_lit_activity_flag                true
% 15.24/2.50  --inst_restr_to_given                   false
% 15.24/2.50  --inst_activity_threshold               500
% 15.24/2.50  --inst_out_proof                        true
% 15.24/2.50  
% 15.24/2.50  ------ Resolution Options
% 15.24/2.50  
% 15.24/2.50  --resolution_flag                       false
% 15.24/2.50  --res_lit_sel                           adaptive
% 15.24/2.50  --res_lit_sel_side                      none
% 15.24/2.50  --res_ordering                          kbo
% 15.24/2.50  --res_to_prop_solver                    active
% 15.24/2.50  --res_prop_simpl_new                    false
% 15.24/2.50  --res_prop_simpl_given                  true
% 15.24/2.50  --res_passive_queue_type                priority_queues
% 15.24/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.24/2.50  --res_passive_queues_freq               [15;5]
% 15.24/2.50  --res_forward_subs                      full
% 15.24/2.50  --res_backward_subs                     full
% 15.24/2.50  --res_forward_subs_resolution           true
% 15.24/2.50  --res_backward_subs_resolution          true
% 15.24/2.50  --res_orphan_elimination                true
% 15.24/2.50  --res_time_limit                        2.
% 15.24/2.50  --res_out_proof                         true
% 15.24/2.50  
% 15.24/2.50  ------ Superposition Options
% 15.24/2.50  
% 15.24/2.50  --superposition_flag                    true
% 15.24/2.50  --sup_passive_queue_type                priority_queues
% 15.24/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.24/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.24/2.50  --demod_completeness_check              fast
% 15.24/2.50  --demod_use_ground                      true
% 15.24/2.50  --sup_to_prop_solver                    passive
% 15.24/2.50  --sup_prop_simpl_new                    true
% 15.24/2.50  --sup_prop_simpl_given                  true
% 15.24/2.50  --sup_fun_splitting                     true
% 15.24/2.50  --sup_smt_interval                      50000
% 15.24/2.50  
% 15.24/2.50  ------ Superposition Simplification Setup
% 15.24/2.50  
% 15.24/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.24/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.24/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.24/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.24/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.24/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.24/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.24/2.50  --sup_immed_triv                        [TrivRules]
% 15.24/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.50  --sup_immed_bw_main                     []
% 15.24/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.24/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.24/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.50  --sup_input_bw                          []
% 15.24/2.50  
% 15.24/2.50  ------ Combination Options
% 15.24/2.50  
% 15.24/2.50  --comb_res_mult                         3
% 15.24/2.50  --comb_sup_mult                         2
% 15.24/2.50  --comb_inst_mult                        10
% 15.24/2.50  
% 15.24/2.50  ------ Debug Options
% 15.24/2.50  
% 15.24/2.50  --dbg_backtrace                         false
% 15.24/2.50  --dbg_dump_prop_clauses                 false
% 15.24/2.50  --dbg_dump_prop_clauses_file            -
% 15.24/2.50  --dbg_out_stat                          false
% 15.24/2.50  
% 15.24/2.50  
% 15.24/2.50  
% 15.24/2.50  
% 15.24/2.50  ------ Proving...
% 15.24/2.50  
% 15.24/2.50  
% 15.24/2.50  % SZS status Theorem for theBenchmark.p
% 15.24/2.50  
% 15.24/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.24/2.50  
% 15.24/2.50  fof(f21,conjecture,(
% 15.24/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f22,negated_conjecture,(
% 15.24/2.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 15.24/2.50    inference(negated_conjecture,[],[f21])).
% 15.24/2.50  
% 15.24/2.50  fof(f45,plain,(
% 15.24/2.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 15.24/2.50    inference(ennf_transformation,[],[f22])).
% 15.24/2.50  
% 15.24/2.50  fof(f46,plain,(
% 15.24/2.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.24/2.50    inference(flattening,[],[f45])).
% 15.24/2.50  
% 15.24/2.50  fof(f63,plain,(
% 15.24/2.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.24/2.50    inference(nnf_transformation,[],[f46])).
% 15.24/2.50  
% 15.24/2.50  fof(f64,plain,(
% 15.24/2.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.24/2.50    inference(flattening,[],[f63])).
% 15.24/2.50  
% 15.24/2.50  fof(f68,plain,(
% 15.24/2.50    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK6 = X2 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK6))) )),
% 15.24/2.50    introduced(choice_axiom,[])).
% 15.24/2.50  
% 15.24/2.50  fof(f67,plain,(
% 15.24/2.50    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK5,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK5,X0,X1)) & sK5 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 15.24/2.50    introduced(choice_axiom,[])).
% 15.24/2.50  
% 15.24/2.50  fof(f66,plain,(
% 15.24/2.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(X2,X0,sK4)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(X2,X0,sK4)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4)) & v1_funct_1(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))) )),
% 15.24/2.50    introduced(choice_axiom,[])).
% 15.24/2.50  
% 15.24/2.50  fof(f65,plain,(
% 15.24/2.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK3,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK3,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 15.24/2.50    introduced(choice_axiom,[])).
% 15.24/2.50  
% 15.24/2.50  fof(f69,plain,(
% 15.24/2.50    ((((~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(sK5,sK3,sK4)) & (v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,sK3,sK4)) & sK5 = sK6 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 15.24/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f64,f68,f67,f66,f65])).
% 15.24/2.50  
% 15.24/2.50  fof(f110,plain,(
% 15.24/2.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 15.24/2.50    inference(cnf_transformation,[],[f69])).
% 15.24/2.50  
% 15.24/2.50  fof(f114,plain,(
% 15.24/2.50    sK5 = sK6),
% 15.24/2.50    inference(cnf_transformation,[],[f69])).
% 15.24/2.50  
% 15.24/2.50  fof(f15,axiom,(
% 15.24/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f35,plain,(
% 15.24/2.50    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.24/2.50    inference(ennf_transformation,[],[f15])).
% 15.24/2.50  
% 15.24/2.50  fof(f36,plain,(
% 15.24/2.50    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.24/2.50    inference(flattening,[],[f35])).
% 15.24/2.50  
% 15.24/2.50  fof(f95,plain,(
% 15.24/2.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.24/2.50    inference(cnf_transformation,[],[f36])).
% 15.24/2.50  
% 15.24/2.50  fof(f13,axiom,(
% 15.24/2.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f33,plain,(
% 15.24/2.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 15.24/2.50    inference(ennf_transformation,[],[f13])).
% 15.24/2.50  
% 15.24/2.50  fof(f34,plain,(
% 15.24/2.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.24/2.50    inference(flattening,[],[f33])).
% 15.24/2.50  
% 15.24/2.50  fof(f58,plain,(
% 15.24/2.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.24/2.50    inference(nnf_transformation,[],[f34])).
% 15.24/2.50  
% 15.24/2.50  fof(f88,plain,(
% 15.24/2.50    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.24/2.50    inference(cnf_transformation,[],[f58])).
% 15.24/2.50  
% 15.24/2.50  fof(f11,axiom,(
% 15.24/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f26,plain,(
% 15.24/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 15.24/2.50    inference(pure_predicate_removal,[],[f11])).
% 15.24/2.50  
% 15.24/2.50  fof(f31,plain,(
% 15.24/2.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.24/2.50    inference(ennf_transformation,[],[f26])).
% 15.24/2.50  
% 15.24/2.50  fof(f86,plain,(
% 15.24/2.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.24/2.50    inference(cnf_transformation,[],[f31])).
% 15.24/2.50  
% 15.24/2.50  fof(f10,axiom,(
% 15.24/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f30,plain,(
% 15.24/2.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.24/2.50    inference(ennf_transformation,[],[f10])).
% 15.24/2.50  
% 15.24/2.50  fof(f85,plain,(
% 15.24/2.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.24/2.50    inference(cnf_transformation,[],[f30])).
% 15.24/2.50  
% 15.24/2.50  fof(f111,plain,(
% 15.24/2.50    v1_funct_1(sK6)),
% 15.24/2.50    inference(cnf_transformation,[],[f69])).
% 15.24/2.50  
% 15.24/2.50  fof(f109,plain,(
% 15.24/2.50    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))),
% 15.24/2.50    inference(cnf_transformation,[],[f69])).
% 15.24/2.50  
% 15.24/2.50  fof(f12,axiom,(
% 15.24/2.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f32,plain,(
% 15.24/2.50    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 15.24/2.50    inference(ennf_transformation,[],[f12])).
% 15.24/2.50  
% 15.24/2.50  fof(f87,plain,(
% 15.24/2.50    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 15.24/2.50    inference(cnf_transformation,[],[f32])).
% 15.24/2.50  
% 15.24/2.50  fof(f3,axiom,(
% 15.24/2.50    v1_xboole_0(k1_xboole_0)),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f75,plain,(
% 15.24/2.50    v1_xboole_0(k1_xboole_0)),
% 15.24/2.50    inference(cnf_transformation,[],[f3])).
% 15.24/2.50  
% 15.24/2.50  fof(f5,axiom,(
% 15.24/2.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f55,plain,(
% 15.24/2.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.24/2.50    inference(nnf_transformation,[],[f5])).
% 15.24/2.50  
% 15.24/2.50  fof(f56,plain,(
% 15.24/2.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.24/2.50    inference(flattening,[],[f55])).
% 15.24/2.50  
% 15.24/2.50  fof(f79,plain,(
% 15.24/2.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 15.24/2.50    inference(cnf_transformation,[],[f56])).
% 15.24/2.50  
% 15.24/2.50  fof(f117,plain,(
% 15.24/2.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 15.24/2.50    inference(equality_resolution,[],[f79])).
% 15.24/2.50  
% 15.24/2.50  fof(f78,plain,(
% 15.24/2.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 15.24/2.50    inference(cnf_transformation,[],[f56])).
% 15.24/2.50  
% 15.24/2.50  fof(f118,plain,(
% 15.24/2.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 15.24/2.50    inference(equality_resolution,[],[f78])).
% 15.24/2.50  
% 15.24/2.50  fof(f4,axiom,(
% 15.24/2.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f28,plain,(
% 15.24/2.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 15.24/2.50    inference(ennf_transformation,[],[f4])).
% 15.24/2.50  
% 15.24/2.50  fof(f76,plain,(
% 15.24/2.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 15.24/2.50    inference(cnf_transformation,[],[f28])).
% 15.24/2.50  
% 15.24/2.50  fof(f113,plain,(
% 15.24/2.50    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),
% 15.24/2.50    inference(cnf_transformation,[],[f69])).
% 15.24/2.50  
% 15.24/2.50  fof(f112,plain,(
% 15.24/2.50    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),
% 15.24/2.50    inference(cnf_transformation,[],[f69])).
% 15.24/2.50  
% 15.24/2.50  fof(f20,axiom,(
% 15.24/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f43,plain,(
% 15.24/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.24/2.50    inference(ennf_transformation,[],[f20])).
% 15.24/2.50  
% 15.24/2.50  fof(f44,plain,(
% 15.24/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.24/2.50    inference(flattening,[],[f43])).
% 15.24/2.50  
% 15.24/2.50  fof(f62,plain,(
% 15.24/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.24/2.50    inference(nnf_transformation,[],[f44])).
% 15.24/2.50  
% 15.24/2.50  fof(f103,plain,(
% 15.24/2.50    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.24/2.50    inference(cnf_transformation,[],[f62])).
% 15.24/2.50  
% 15.24/2.50  fof(f123,plain,(
% 15.24/2.50    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.24/2.50    inference(equality_resolution,[],[f103])).
% 15.24/2.50  
% 15.24/2.50  fof(f104,plain,(
% 15.24/2.50    v2_pre_topc(sK3)),
% 15.24/2.50    inference(cnf_transformation,[],[f69])).
% 15.24/2.50  
% 15.24/2.50  fof(f105,plain,(
% 15.24/2.50    l1_pre_topc(sK3)),
% 15.24/2.50    inference(cnf_transformation,[],[f69])).
% 15.24/2.50  
% 15.24/2.50  fof(f106,plain,(
% 15.24/2.50    v2_pre_topc(sK4)),
% 15.24/2.50    inference(cnf_transformation,[],[f69])).
% 15.24/2.50  
% 15.24/2.50  fof(f107,plain,(
% 15.24/2.50    l1_pre_topc(sK4)),
% 15.24/2.50    inference(cnf_transformation,[],[f69])).
% 15.24/2.50  
% 15.24/2.50  fof(f115,plain,(
% 15.24/2.50    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,sK3,sK4)),
% 15.24/2.50    inference(cnf_transformation,[],[f69])).
% 15.24/2.50  
% 15.24/2.50  fof(f18,axiom,(
% 15.24/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f23,plain,(
% 15.24/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 15.24/2.50    inference(pure_predicate_removal,[],[f18])).
% 15.24/2.50  
% 15.24/2.50  fof(f39,plain,(
% 15.24/2.50    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.24/2.50    inference(ennf_transformation,[],[f23])).
% 15.24/2.50  
% 15.24/2.50  fof(f40,plain,(
% 15.24/2.50    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.24/2.50    inference(flattening,[],[f39])).
% 15.24/2.50  
% 15.24/2.50  fof(f99,plain,(
% 15.24/2.50    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.24/2.50    inference(cnf_transformation,[],[f40])).
% 15.24/2.50  
% 15.24/2.50  fof(f16,axiom,(
% 15.24/2.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f24,plain,(
% 15.24/2.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 15.24/2.50    inference(pure_predicate_removal,[],[f16])).
% 15.24/2.50  
% 15.24/2.50  fof(f37,plain,(
% 15.24/2.50    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 15.24/2.50    inference(ennf_transformation,[],[f24])).
% 15.24/2.50  
% 15.24/2.50  fof(f97,plain,(
% 15.24/2.50    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.24/2.50    inference(cnf_transformation,[],[f37])).
% 15.24/2.50  
% 15.24/2.50  fof(f17,axiom,(
% 15.24/2.50    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f38,plain,(
% 15.24/2.50    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.24/2.50    inference(ennf_transformation,[],[f17])).
% 15.24/2.50  
% 15.24/2.50  fof(f98,plain,(
% 15.24/2.50    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 15.24/2.50    inference(cnf_transformation,[],[f38])).
% 15.24/2.50  
% 15.24/2.50  fof(f102,plain,(
% 15.24/2.50    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.24/2.50    inference(cnf_transformation,[],[f62])).
% 15.24/2.50  
% 15.24/2.50  fof(f124,plain,(
% 15.24/2.50    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.24/2.50    inference(equality_resolution,[],[f102])).
% 15.24/2.50  
% 15.24/2.50  fof(f116,plain,(
% 15.24/2.50    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(sK5,sK3,sK4)),
% 15.24/2.50    inference(cnf_transformation,[],[f69])).
% 15.24/2.50  
% 15.24/2.50  fof(f19,axiom,(
% 15.24/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f41,plain,(
% 15.24/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.24/2.50    inference(ennf_transformation,[],[f19])).
% 15.24/2.50  
% 15.24/2.50  fof(f42,plain,(
% 15.24/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.24/2.50    inference(flattening,[],[f41])).
% 15.24/2.50  
% 15.24/2.50  fof(f61,plain,(
% 15.24/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.24/2.50    inference(nnf_transformation,[],[f42])).
% 15.24/2.50  
% 15.24/2.50  fof(f101,plain,(
% 15.24/2.50    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.24/2.50    inference(cnf_transformation,[],[f61])).
% 15.24/2.50  
% 15.24/2.50  fof(f121,plain,(
% 15.24/2.50    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.24/2.50    inference(equality_resolution,[],[f101])).
% 15.24/2.50  
% 15.24/2.50  fof(f100,plain,(
% 15.24/2.50    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.24/2.50    inference(cnf_transformation,[],[f61])).
% 15.24/2.50  
% 15.24/2.50  fof(f122,plain,(
% 15.24/2.50    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.24/2.50    inference(equality_resolution,[],[f100])).
% 15.24/2.50  
% 15.24/2.50  fof(f8,axiom,(
% 15.24/2.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f57,plain,(
% 15.24/2.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.24/2.50    inference(nnf_transformation,[],[f8])).
% 15.24/2.50  
% 15.24/2.50  fof(f83,plain,(
% 15.24/2.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.24/2.50    inference(cnf_transformation,[],[f57])).
% 15.24/2.50  
% 15.24/2.50  fof(f14,axiom,(
% 15.24/2.50    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f25,plain,(
% 15.24/2.50    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.24/2.50    inference(pure_predicate_removal,[],[f14])).
% 15.24/2.50  
% 15.24/2.50  fof(f59,plain,(
% 15.24/2.50    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK2(X0,X1),X0,X1) & v1_funct_1(sK2(X0,X1)) & v4_relat_1(sK2(X0,X1),X0) & v1_relat_1(sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.24/2.50    introduced(choice_axiom,[])).
% 15.24/2.50  
% 15.24/2.50  fof(f60,plain,(
% 15.24/2.50    ! [X0,X1] : (v1_funct_2(sK2(X0,X1),X0,X1) & v1_funct_1(sK2(X0,X1)) & v4_relat_1(sK2(X0,X1),X0) & v1_relat_1(sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.24/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f59])).
% 15.24/2.50  
% 15.24/2.50  fof(f94,plain,(
% 15.24/2.50    ( ! [X0,X1] : (v1_funct_2(sK2(X0,X1),X0,X1)) )),
% 15.24/2.50    inference(cnf_transformation,[],[f60])).
% 15.24/2.50  
% 15.24/2.50  fof(f77,plain,(
% 15.24/2.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 15.24/2.50    inference(cnf_transformation,[],[f56])).
% 15.24/2.50  
% 15.24/2.50  fof(f7,axiom,(
% 15.24/2.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f81,plain,(
% 15.24/2.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 15.24/2.50    inference(cnf_transformation,[],[f7])).
% 15.24/2.50  
% 15.24/2.50  fof(f6,axiom,(
% 15.24/2.50    ! [X0] : k2_subset_1(X0) = X0),
% 15.24/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.50  
% 15.24/2.50  fof(f80,plain,(
% 15.24/2.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 15.24/2.50    inference(cnf_transformation,[],[f6])).
% 15.24/2.50  
% 15.24/2.50  fof(f96,plain,(
% 15.24/2.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.24/2.50    inference(cnf_transformation,[],[f36])).
% 15.24/2.50  
% 15.24/2.50  fof(f120,plain,(
% 15.24/2.50    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 15.24/2.50    inference(equality_resolution,[],[f96])).
% 15.24/2.50  
% 15.24/2.50  fof(f90,plain,(
% 15.24/2.50    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.24/2.50    inference(cnf_transformation,[],[f60])).
% 15.24/2.50  
% 15.24/2.50  cnf(c_40,negated_conjecture,
% 15.24/2.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
% 15.24/2.50      inference(cnf_transformation,[],[f110]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3461,plain,
% 15.24/2.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_36,negated_conjecture,
% 15.24/2.50      ( sK5 = sK6 ),
% 15.24/2.50      inference(cnf_transformation,[],[f114]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3491,plain,
% 15.24/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 15.24/2.50      inference(light_normalisation,[status(thm)],[c_3461,c_36]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_26,plain,
% 15.24/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.24/2.50      | v1_partfun1(X0,X1)
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.24/2.50      | ~ v1_funct_1(X0)
% 15.24/2.50      | k1_xboole_0 = X2 ),
% 15.24/2.50      inference(cnf_transformation,[],[f95]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_19,plain,
% 15.24/2.50      ( ~ v1_partfun1(X0,X1)
% 15.24/2.50      | ~ v4_relat_1(X0,X1)
% 15.24/2.50      | ~ v1_relat_1(X0)
% 15.24/2.50      | k1_relat_1(X0) = X1 ),
% 15.24/2.50      inference(cnf_transformation,[],[f88]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_715,plain,
% 15.24/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.24/2.50      | ~ v4_relat_1(X0,X1)
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.24/2.50      | ~ v1_funct_1(X0)
% 15.24/2.50      | ~ v1_relat_1(X0)
% 15.24/2.50      | k1_relat_1(X0) = X1
% 15.24/2.50      | k1_xboole_0 = X2 ),
% 15.24/2.50      inference(resolution,[status(thm)],[c_26,c_19]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_16,plain,
% 15.24/2.50      ( v4_relat_1(X0,X1)
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 15.24/2.50      inference(cnf_transformation,[],[f86]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_15,plain,
% 15.24/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.24/2.50      | v1_relat_1(X0) ),
% 15.24/2.50      inference(cnf_transformation,[],[f85]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_719,plain,
% 15.24/2.50      ( ~ v1_funct_1(X0)
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.24/2.50      | ~ v1_funct_2(X0,X1,X2)
% 15.24/2.50      | k1_relat_1(X0) = X1
% 15.24/2.50      | k1_xboole_0 = X2 ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_715,c_16,c_15]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_720,plain,
% 15.24/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.24/2.50      | ~ v1_funct_1(X0)
% 15.24/2.50      | k1_relat_1(X0) = X1
% 15.24/2.50      | k1_xboole_0 = X2 ),
% 15.24/2.50      inference(renaming,[status(thm)],[c_719]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3453,plain,
% 15.24/2.50      ( k1_relat_1(X0) = X1
% 15.24/2.50      | k1_xboole_0 = X2
% 15.24/2.50      | v1_funct_2(X0,X1,X2) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3774,plain,
% 15.24/2.50      ( u1_struct_0(sK4) = k1_xboole_0
% 15.24/2.50      | u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | v1_funct_1(sK6) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_3491,c_3453]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_39,negated_conjecture,
% 15.24/2.50      ( v1_funct_1(sK6) ),
% 15.24/2.50      inference(cnf_transformation,[],[f111]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_41,negated_conjecture,
% 15.24/2.50      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 15.24/2.50      inference(cnf_transformation,[],[f109]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3460,plain,
% 15.24/2.50      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3490,plain,
% 15.24/2.50      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 15.24/2.50      inference(light_normalisation,[status(thm)],[c_3460,c_36]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3532,plain,
% 15.24/2.50      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 15.24/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_3490]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3775,plain,
% 15.24/2.50      ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 15.24/2.50      | ~ v1_funct_1(sK6)
% 15.24/2.50      | u1_struct_0(sK4) = k1_xboole_0
% 15.24/2.50      | u1_struct_0(sK3) = k1_relat_1(sK6) ),
% 15.24/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_3774]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4101,plain,
% 15.24/2.50      ( u1_struct_0(sK4) = k1_xboole_0
% 15.24/2.50      | u1_struct_0(sK3) = k1_relat_1(sK6) ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_3774,c_39,c_3532,c_3775]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_17,plain,
% 15.24/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.24/2.50      | ~ v1_xboole_0(X2)
% 15.24/2.50      | v1_xboole_0(X0) ),
% 15.24/2.50      inference(cnf_transformation,[],[f87]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3477,plain,
% 15.24/2.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.24/2.50      | v1_xboole_0(X2) != iProver_top
% 15.24/2.50      | v1_xboole_0(X0) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6974,plain,
% 15.24/2.50      ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | v1_xboole_0(sK6) = iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_3491,c_3477]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_7014,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v1_xboole_0(sK6) = iProver_top
% 15.24/2.50      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_4101,c_6974]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_5,plain,
% 15.24/2.50      ( v1_xboole_0(k1_xboole_0) ),
% 15.24/2.50      inference(cnf_transformation,[],[f75]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_132,plain,
% 15.24/2.50      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4107,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0))) = iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_4101,c_3491]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_7,plain,
% 15.24/2.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.24/2.50      inference(cnf_transformation,[],[f117]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4109,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_4107,c_7]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_8,plain,
% 15.24/2.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.24/2.50      inference(cnf_transformation,[],[f118]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6979,plain,
% 15.24/2.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.24/2.50      | v1_xboole_0(X1) != iProver_top
% 15.24/2.50      | v1_xboole_0(X0) = iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_8,c_3477]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_7001,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v1_xboole_0(X0) != iProver_top
% 15.24/2.50      | v1_xboole_0(sK6) = iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_4109,c_6979]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_7009,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v1_xboole_0(sK6) = iProver_top
% 15.24/2.50      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_7001]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_7127,plain,
% 15.24/2.50      ( v1_xboole_0(sK6) = iProver_top
% 15.24/2.50      | u1_struct_0(sK3) = k1_relat_1(sK6) ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_7014,c_132,c_7009]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_7128,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v1_xboole_0(sK6) = iProver_top ),
% 15.24/2.50      inference(renaming,[status(thm)],[c_7127]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6,plain,
% 15.24/2.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 15.24/2.50      inference(cnf_transformation,[],[f76]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3481,plain,
% 15.24/2.50      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_7131,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6) | sK6 = k1_xboole_0 ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_7128,c_3481]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_37,negated_conjecture,
% 15.24/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
% 15.24/2.50      inference(cnf_transformation,[],[f113]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3464,plain,
% 15.24/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_22315,plain,
% 15.24/2.50      ( sK6 = k1_xboole_0
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_7131,c_3464]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_23158,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
% 15.24/2.50      | u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 15.24/2.50      | sK6 = k1_xboole_0
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | v1_funct_1(sK6) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_22315,c_3453]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_54,plain,
% 15.24/2.50      ( v1_funct_1(sK6) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3762,plain,
% 15.24/2.50      ( ~ v1_xboole_0(sK6) | k1_xboole_0 = sK6 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_6]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_2611,plain,( X0 = X0 ),theory(equality) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4121,plain,
% 15.24/2.50      ( sK6 = sK6 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_2611]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_2612,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3787,plain,
% 15.24/2.50      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_2612]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4254,plain,
% 15.24/2.50      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_3787]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4255,plain,
% 15.24/2.50      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_4254]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6972,plain,
% 15.24/2.50      ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | v1_xboole_0(sK6) = iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_3464,c_3477]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6984,plain,
% 15.24/2.50      ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 15.24/2.50      | v1_xboole_0(sK6) ),
% 15.24/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_6972]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_2613,plain,
% 15.24/2.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 15.24/2.50      theory(equality) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_9824,plain,
% 15.24/2.50      ( ~ v1_xboole_0(X0)
% 15.24/2.50      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 15.24/2.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X0 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_2613]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_9826,plain,
% 15.24/2.50      ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 15.24/2.50      | ~ v1_xboole_0(k1_xboole_0)
% 15.24/2.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_xboole_0 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_9824]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_38,negated_conjecture,
% 15.24/2.50      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
% 15.24/2.50      inference(cnf_transformation,[],[f112]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3463,plain,
% 15.24/2.50      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_22316,plain,
% 15.24/2.50      ( sK6 = k1_xboole_0
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_7131,c_3463]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_23383,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 15.24/2.50      | sK6 = k1_xboole_0 ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_23158,c_54,c_5,c_3762,c_4121,c_4255,c_6984,c_9826,
% 15.24/2.50                 c_22316]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_32,plain,
% 15.24/2.50      ( v5_pre_topc(X0,X1,X2)
% 15.24/2.50      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 15.24/2.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.24/2.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 15.24/2.50      | ~ v2_pre_topc(X1)
% 15.24/2.50      | ~ v2_pre_topc(X2)
% 15.24/2.50      | ~ l1_pre_topc(X1)
% 15.24/2.50      | ~ l1_pre_topc(X2)
% 15.24/2.50      | ~ v1_funct_1(X0) ),
% 15.24/2.50      inference(cnf_transformation,[],[f123]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3468,plain,
% 15.24/2.50      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 15.24/2.50      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 15.24/2.50      | v2_pre_topc(X1) != iProver_top
% 15.24/2.50      | v2_pre_topc(X2) != iProver_top
% 15.24/2.50      | l1_pre_topc(X1) != iProver_top
% 15.24/2.50      | l1_pre_topc(X2) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4831,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 15.24/2.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) = iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 15.24/2.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK4) != iProver_top
% 15.24/2.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK4) != iProver_top
% 15.24/2.50      | v1_funct_1(sK6) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_3464,c_3468]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_46,negated_conjecture,
% 15.24/2.50      ( v2_pre_topc(sK3) ),
% 15.24/2.50      inference(cnf_transformation,[],[f104]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_47,plain,
% 15.24/2.50      ( v2_pre_topc(sK3) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_45,negated_conjecture,
% 15.24/2.50      ( l1_pre_topc(sK3) ),
% 15.24/2.50      inference(cnf_transformation,[],[f105]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48,plain,
% 15.24/2.50      ( l1_pre_topc(sK3) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_44,negated_conjecture,
% 15.24/2.50      ( v2_pre_topc(sK4) ),
% 15.24/2.50      inference(cnf_transformation,[],[f106]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_49,plain,
% 15.24/2.50      ( v2_pre_topc(sK4) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_43,negated_conjecture,
% 15.24/2.50      ( l1_pre_topc(sK4) ),
% 15.24/2.50      inference(cnf_transformation,[],[f107]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_50,plain,
% 15.24/2.50      ( l1_pre_topc(sK4) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_55,plain,
% 15.24/2.50      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_35,negated_conjecture,
% 15.24/2.50      ( v5_pre_topc(sK5,sK3,sK4)
% 15.24/2.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 15.24/2.50      inference(cnf_transformation,[],[f115]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3465,plain,
% 15.24/2.50      ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 15.24/2.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3492,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 15.24/2.50      | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
% 15.24/2.50      inference(light_normalisation,[status(thm)],[c_3465,c_36]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_29,plain,
% 15.24/2.50      ( ~ v2_pre_topc(X0)
% 15.24/2.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 15.24/2.50      | ~ l1_pre_topc(X0) ),
% 15.24/2.50      inference(cnf_transformation,[],[f99]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3604,plain,
% 15.24/2.50      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 15.24/2.50      | ~ v2_pre_topc(sK3)
% 15.24/2.50      | ~ l1_pre_topc(sK3) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_29]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3605,plain,
% 15.24/2.50      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 15.24/2.50      | v2_pre_topc(sK3) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK3) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_3604]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_27,plain,
% 15.24/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 15.24/2.50      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 15.24/2.50      inference(cnf_transformation,[],[f97]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3687,plain,
% 15.24/2.50      ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 15.24/2.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_27]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3688,plain,
% 15.24/2.50      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 15.24/2.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_3687]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_28,plain,
% 15.24/2.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 15.24/2.50      | ~ l1_pre_topc(X0) ),
% 15.24/2.50      inference(cnf_transformation,[],[f98]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3794,plain,
% 15.24/2.50      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 15.24/2.50      | ~ l1_pre_topc(sK3) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_28]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3795,plain,
% 15.24/2.50      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
% 15.24/2.50      | l1_pre_topc(sK3) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_3794]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_33,plain,
% 15.24/2.50      ( ~ v5_pre_topc(X0,X1,X2)
% 15.24/2.50      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 15.24/2.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.24/2.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 15.24/2.50      | ~ v2_pre_topc(X1)
% 15.24/2.50      | ~ v2_pre_topc(X2)
% 15.24/2.50      | ~ l1_pre_topc(X1)
% 15.24/2.50      | ~ l1_pre_topc(X2)
% 15.24/2.50      | ~ v1_funct_1(X0) ),
% 15.24/2.50      inference(cnf_transformation,[],[f124]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3467,plain,
% 15.24/2.50      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 15.24/2.50      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 15.24/2.50      | v2_pre_topc(X1) != iProver_top
% 15.24/2.50      | v2_pre_topc(X2) != iProver_top
% 15.24/2.50      | l1_pre_topc(X1) != iProver_top
% 15.24/2.50      | l1_pre_topc(X2) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4309,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 15.24/2.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 15.24/2.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK4) != iProver_top
% 15.24/2.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK4) != iProver_top
% 15.24/2.50      | v1_funct_1(sK6) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_3464,c_3467]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_34,negated_conjecture,
% 15.24/2.50      ( ~ v5_pre_topc(sK5,sK3,sK4)
% 15.24/2.50      | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 15.24/2.50      inference(cnf_transformation,[],[f116]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3466,plain,
% 15.24/2.50      ( v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 15.24/2.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3493,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 15.24/2.50      | v5_pre_topc(sK6,sK3,sK4) != iProver_top ),
% 15.24/2.50      inference(light_normalisation,[status(thm)],[c_3466,c_36]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_30,plain,
% 15.24/2.50      ( v5_pre_topc(X0,X1,X2)
% 15.24/2.50      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 15.24/2.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.24/2.50      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 15.24/2.50      | ~ v2_pre_topc(X1)
% 15.24/2.50      | ~ v2_pre_topc(X2)
% 15.24/2.50      | ~ l1_pre_topc(X1)
% 15.24/2.50      | ~ l1_pre_topc(X2)
% 15.24/2.50      | ~ v1_funct_1(X0) ),
% 15.24/2.50      inference(cnf_transformation,[],[f121]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3712,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,X0,sK4)
% 15.24/2.50      | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK4)
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))))
% 15.24/2.50      | ~ v2_pre_topc(X0)
% 15.24/2.50      | ~ v2_pre_topc(sK4)
% 15.24/2.50      | ~ l1_pre_topc(X0)
% 15.24/2.50      | ~ l1_pre_topc(sK4)
% 15.24/2.50      | ~ v1_funct_1(sK6) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_30]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3928,plain,
% 15.24/2.50      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
% 15.24/2.50      | v5_pre_topc(sK6,sK3,sK4)
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 15.24/2.50      | ~ v2_pre_topc(sK4)
% 15.24/2.50      | ~ v2_pre_topc(sK3)
% 15.24/2.50      | ~ l1_pre_topc(sK4)
% 15.24/2.50      | ~ l1_pre_topc(sK3)
% 15.24/2.50      | ~ v1_funct_1(sK6) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_3712]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3929,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
% 15.24/2.50      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK4) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK3) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK4) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK3) != iProver_top
% 15.24/2.50      | v1_funct_1(sK6) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_3928]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4414,plain,
% 15.24/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_4309,c_47,c_48,c_49,c_50,c_54,c_55,c_3493,c_3491,
% 15.24/2.50                 c_3490,c_3605,c_3688,c_3795,c_3929]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4415,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 15.24/2.50      inference(renaming,[status(thm)],[c_4414]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_31,plain,
% 15.24/2.50      ( ~ v5_pre_topc(X0,X1,X2)
% 15.24/2.50      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 15.24/2.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.24/2.50      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 15.24/2.50      | ~ v2_pre_topc(X1)
% 15.24/2.50      | ~ v2_pre_topc(X2)
% 15.24/2.50      | ~ l1_pre_topc(X1)
% 15.24/2.50      | ~ l1_pre_topc(X2)
% 15.24/2.50      | ~ v1_funct_1(X0) ),
% 15.24/2.50      inference(cnf_transformation,[],[f122]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3893,plain,
% 15.24/2.50      ( ~ v5_pre_topc(sK6,X0,sK4)
% 15.24/2.50      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK4)
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))))
% 15.24/2.50      | ~ v2_pre_topc(X0)
% 15.24/2.50      | ~ v2_pre_topc(sK4)
% 15.24/2.50      | ~ l1_pre_topc(X0)
% 15.24/2.50      | ~ l1_pre_topc(sK4)
% 15.24/2.50      | ~ v1_funct_1(sK6) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_31]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4472,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
% 15.24/2.50      | ~ v5_pre_topc(sK6,sK3,sK4)
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 15.24/2.50      | ~ v2_pre_topc(sK4)
% 15.24/2.50      | ~ v2_pre_topc(sK3)
% 15.24/2.50      | ~ l1_pre_topc(sK4)
% 15.24/2.50      | ~ l1_pre_topc(sK3)
% 15.24/2.50      | ~ v1_funct_1(sK6) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_3893]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4473,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) = iProver_top
% 15.24/2.50      | v5_pre_topc(sK6,sK3,sK4) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK4) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK3) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK4) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK3) != iProver_top
% 15.24/2.50      | v1_funct_1(sK6) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_4472]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4941,plain,
% 15.24/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_4831,c_47,c_48,c_49,c_50,c_54,c_55,c_3492,c_3491,
% 15.24/2.50                 c_3490,c_3605,c_3688,c_3795,c_4415,c_4473]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4942,plain,
% 15.24/2.50      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 15.24/2.50      inference(renaming,[status(thm)],[c_4941]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_22306,plain,
% 15.24/2.50      ( sK6 = k1_xboole_0
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_7131,c_4942]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_23504,plain,
% 15.24/2.50      ( sK6 = k1_xboole_0
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK4)))) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_23383,c_22306]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_23506,plain,
% 15.24/2.50      ( sK6 = k1_xboole_0
% 15.24/2.50      | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_23383,c_22316]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_23505,plain,
% 15.24/2.50      ( sK6 = k1_xboole_0
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_23383,c_22315]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3469,plain,
% 15.24/2.50      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 15.24/2.50      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 15.24/2.50      | v2_pre_topc(X1) != iProver_top
% 15.24/2.50      | v2_pre_topc(X2) != iProver_top
% 15.24/2.50      | l1_pre_topc(X1) != iProver_top
% 15.24/2.50      | l1_pre_topc(X2) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_5385,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 15.24/2.50      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 15.24/2.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK3) != iProver_top
% 15.24/2.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK3) != iProver_top
% 15.24/2.50      | v1_funct_1(sK6) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_3464,c_3469]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_56,plain,
% 15.24/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3619,plain,
% 15.24/2.50      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 15.24/2.50      | ~ v2_pre_topc(sK4)
% 15.24/2.50      | ~ l1_pre_topc(sK4) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_29]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3620,plain,
% 15.24/2.50      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 15.24/2.50      | v2_pre_topc(sK4) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK4) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_3619]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3697,plain,
% 15.24/2.50      ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 15.24/2.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_27]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3698,plain,
% 15.24/2.50      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 15.24/2.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_3697]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3822,plain,
% 15.24/2.50      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 15.24/2.50      | ~ l1_pre_topc(sK4) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_28]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3823,plain,
% 15.24/2.50      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
% 15.24/2.50      | l1_pre_topc(sK4) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_3822]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3713,plain,
% 15.24/2.50      ( ~ v5_pre_topc(sK6,X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 15.24/2.50      | v5_pre_topc(sK6,X0,sK4)
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
% 15.24/2.50      | ~ v2_pre_topc(X0)
% 15.24/2.50      | ~ v2_pre_topc(sK4)
% 15.24/2.50      | ~ l1_pre_topc(X0)
% 15.24/2.50      | ~ l1_pre_topc(sK4)
% 15.24/2.50      | ~ v1_funct_1(sK6) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_32]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3902,plain,
% 15.24/2.50      ( ~ v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 15.24/2.50      | v5_pre_topc(sK6,sK3,sK4)
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 15.24/2.50      | ~ v2_pre_topc(sK4)
% 15.24/2.50      | ~ v2_pre_topc(sK3)
% 15.24/2.50      | ~ l1_pre_topc(sK4)
% 15.24/2.50      | ~ l1_pre_topc(sK3)
% 15.24/2.50      | ~ v1_funct_1(sK6) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_3713]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3903,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 15.24/2.50      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK4) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK3) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK4) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK3) != iProver_top
% 15.24/2.50      | v1_funct_1(sK6) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_3902]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3965,plain,
% 15.24/2.50      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 15.24/2.50      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 15.24/2.50      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 15.24/2.50      | ~ v2_pre_topc(sK3)
% 15.24/2.50      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 15.24/2.50      | ~ l1_pre_topc(sK3)
% 15.24/2.50      | ~ v1_funct_1(sK6) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_30]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3969,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 15.24/2.50      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 15.24/2.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK3) != iProver_top
% 15.24/2.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK3) != iProver_top
% 15.24/2.50      | v1_funct_1(sK6) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_3965]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3971,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 15.24/2.50      | ~ v5_pre_topc(sK6,sK3,sK4)
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 15.24/2.50      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 15.24/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 15.24/2.50      | ~ v2_pre_topc(sK4)
% 15.24/2.50      | ~ v2_pre_topc(sK3)
% 15.24/2.50      | ~ l1_pre_topc(sK4)
% 15.24/2.50      | ~ l1_pre_topc(sK3)
% 15.24/2.50      | ~ v1_funct_1(sK6) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_33]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3972,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 15.24/2.50      | v5_pre_topc(sK6,sK3,sK4) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK4) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK3) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK4) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK3) != iProver_top
% 15.24/2.50      | v1_funct_1(sK6) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_3971]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_5969,plain,
% 15.24/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_5385,c_47,c_48,c_49,c_50,c_54,c_55,c_56,c_3493,c_3492,
% 15.24/2.50                 c_3491,c_3490,c_3620,c_3698,c_3823,c_3903,c_3969,c_3972]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_5970,plain,
% 15.24/2.50      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 15.24/2.50      inference(renaming,[status(thm)],[c_5969]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_5973,plain,
% 15.24/2.50      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_5970,c_47,c_48,c_49,c_50,c_54,c_55,c_56,c_3492,c_3491,
% 15.24/2.50                 c_3490,c_3620,c_3698,c_3823,c_3969,c_3972]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_22301,plain,
% 15.24/2.50      ( sK6 = k1_xboole_0
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_7131,c_5973]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_23848,plain,
% 15.24/2.50      ( sK6 = k1_xboole_0
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_23505,c_22301]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_28791,plain,
% 15.24/2.50      ( sK6 = k1_xboole_0
% 15.24/2.50      | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_7131,c_23848]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_28859,plain,
% 15.24/2.50      ( sK6 = k1_xboole_0 ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_23504,c_23506,c_28791]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_29130,plain,
% 15.24/2.50      ( u1_struct_0(sK4) = k1_xboole_0
% 15.24/2.50      | u1_struct_0(sK3) = k1_relat_1(k1_xboole_0) ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_28859,c_4101]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_12,plain,
% 15.24/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.24/2.50      inference(cnf_transformation,[],[f83]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3479,plain,
% 15.24/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 15.24/2.50      | r1_tarski(X0,X1) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3470,plain,
% 15.24/2.50      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 15.24/2.50      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 15.24/2.50      | v2_pre_topc(X1) != iProver_top
% 15.24/2.50      | v2_pre_topc(X2) != iProver_top
% 15.24/2.50      | l1_pre_topc(X1) != iProver_top
% 15.24/2.50      | l1_pre_topc(X2) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6599,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),X1) != iProver_top
% 15.24/2.50      | v5_pre_topc(X0,sK4,X1) = iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(X1)) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))),u1_struct_0(X1)))) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) != iProver_top
% 15.24/2.50      | v2_pre_topc(X1) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK4) != iProver_top
% 15.24/2.50      | l1_pre_topc(X1) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK4) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_4101,c_3470]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_7543,plain,
% 15.24/2.50      ( l1_pre_topc(X1) != iProver_top
% 15.24/2.50      | u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),X1) != iProver_top
% 15.24/2.50      | v5_pre_topc(X0,sK4,X1) = iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(X1)) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))),u1_struct_0(X1)))) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) != iProver_top
% 15.24/2.50      | v2_pre_topc(X1) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_6599,c_49,c_50]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_7544,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),X1) != iProver_top
% 15.24/2.50      | v5_pre_topc(X0,sK4,X1) = iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(X1)) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))),u1_struct_0(X1)))) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) != iProver_top
% 15.24/2.50      | v2_pre_topc(X1) != iProver_top
% 15.24/2.50      | l1_pre_topc(X1) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(renaming,[status(thm)],[c_7543]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_7549,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),X1) != iProver_top
% 15.24/2.50      | v5_pre_topc(X0,sK4,X1) = iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(X1)) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) != iProver_top
% 15.24/2.50      | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))),u1_struct_0(X1))) != iProver_top
% 15.24/2.50      | v2_pre_topc(X1) != iProver_top
% 15.24/2.50      | l1_pre_topc(X1) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_3479,c_7544]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48122,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
% 15.24/2.50      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),X1) != iProver_top
% 15.24/2.50      | v5_pre_topc(X0,sK4,X1) = iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(X1)) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) != iProver_top
% 15.24/2.50      | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))),u1_struct_0(X1))) != iProver_top
% 15.24/2.50      | v2_pre_topc(X1) != iProver_top
% 15.24/2.50      | l1_pre_topc(X1) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(light_normalisation,[status(thm)],[c_7549,c_28859]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48129,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
% 15.24/2.50      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK4) != iProver_top
% 15.24/2.50      | v5_pre_topc(X0,sK4,sK4) = iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_xboole_0) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
% 15.24/2.50      | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))),u1_struct_0(sK4))) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK4) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK4) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_29130,c_48122]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_20,plain,
% 15.24/2.50      ( v1_funct_2(sK2(X0,X1),X0,X1) ),
% 15.24/2.50      inference(cnf_transformation,[],[f94]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_99,plain,
% 15.24/2.50      ( v1_funct_2(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_20]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_98,plain,
% 15.24/2.50      ( v1_funct_2(sK2(X0,X1),X0,X1) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_100,plain,
% 15.24/2.50      ( v1_funct_2(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_98]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_9,plain,
% 15.24/2.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 15.24/2.50      | k1_xboole_0 = X0
% 15.24/2.50      | k1_xboole_0 = X1 ),
% 15.24/2.50      inference(cnf_transformation,[],[f77]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_127,plain,
% 15.24/2.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 15.24/2.50      | k1_xboole_0 = k1_xboole_0 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_9]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_128,plain,
% 15.24/2.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_8]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_11,plain,
% 15.24/2.50      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 15.24/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3480,plain,
% 15.24/2.50      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_10,plain,
% 15.24/2.50      ( k2_subset_1(X0) = X0 ),
% 15.24/2.50      inference(cnf_transformation,[],[f80]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3489,plain,
% 15.24/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.24/2.50      inference(light_normalisation,[status(thm)],[c_3480,c_10]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3513,plain,
% 15.24/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 15.24/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_3489]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3515,plain,
% 15.24/2.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_3513]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_25,plain,
% 15.24/2.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 15.24/2.50      | v1_partfun1(X0,k1_xboole_0)
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 15.24/2.50      | ~ v1_funct_1(X0) ),
% 15.24/2.50      inference(cnf_transformation,[],[f120]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_743,plain,
% 15.24/2.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 15.24/2.50      | ~ v4_relat_1(X2,X3)
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 15.24/2.50      | ~ v1_funct_1(X0)
% 15.24/2.50      | ~ v1_relat_1(X2)
% 15.24/2.50      | X0 != X2
% 15.24/2.50      | k1_relat_1(X2) = X3
% 15.24/2.50      | k1_xboole_0 != X3 ),
% 15.24/2.50      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_744,plain,
% 15.24/2.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 15.24/2.50      | ~ v4_relat_1(X0,k1_xboole_0)
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 15.24/2.50      | ~ v1_funct_1(X0)
% 15.24/2.50      | ~ v1_relat_1(X0)
% 15.24/2.50      | k1_relat_1(X0) = k1_xboole_0 ),
% 15.24/2.50      inference(unflattening,[status(thm)],[c_743]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_760,plain,
% 15.24/2.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 15.24/2.50      | ~ v1_funct_1(X0)
% 15.24/2.50      | k1_relat_1(X0) = k1_xboole_0 ),
% 15.24/2.50      inference(forward_subsumption_resolution,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_744,c_15,c_16]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3452,plain,
% 15.24/2.50      ( k1_relat_1(X0) = k1_xboole_0
% 15.24/2.50      | v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_760]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3494,plain,
% 15.24/2.50      ( k1_relat_1(X0) = k1_xboole_0
% 15.24/2.50      | v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_3452,c_8]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3521,plain,
% 15.24/2.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 15.24/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 15.24/2.50      | ~ v1_funct_1(X0)
% 15.24/2.50      | k1_relat_1(X0) = k1_xboole_0 ),
% 15.24/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_3494]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3523,plain,
% 15.24/2.50      ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 15.24/2.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 15.24/2.50      | ~ v1_funct_1(k1_xboole_0)
% 15.24/2.50      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_3521]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3673,plain,
% 15.24/2.50      ( X0 != X1 | X0 = sK6 | sK6 != X1 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_2612]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3674,plain,
% 15.24/2.50      ( sK6 != k1_xboole_0
% 15.24/2.50      | k1_xboole_0 = sK6
% 15.24/2.50      | k1_xboole_0 != k1_xboole_0 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_3673]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_2619,plain,
% 15.24/2.50      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 15.24/2.50      theory(equality) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4806,plain,
% 15.24/2.50      ( v1_funct_1(X0) | ~ v1_funct_1(sK6) | X0 != sK6 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_2619]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4808,plain,
% 15.24/2.50      ( ~ v1_funct_1(sK6)
% 15.24/2.50      | v1_funct_1(k1_xboole_0)
% 15.24/2.50      | k1_xboole_0 != sK6 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_4806]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_2618,plain,
% 15.24/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.24/2.50      | v1_funct_2(X3,X4,X5)
% 15.24/2.50      | X3 != X0
% 15.24/2.50      | X4 != X1
% 15.24/2.50      | X5 != X2 ),
% 15.24/2.50      theory(equality) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6675,plain,
% 15.24/2.50      ( v1_funct_2(X0,X1,X2)
% 15.24/2.50      | ~ v1_funct_2(sK2(X3,X4),X3,X4)
% 15.24/2.50      | X1 != X3
% 15.24/2.50      | X2 != X4
% 15.24/2.50      | X0 != sK2(X3,X4) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_2618]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6677,plain,
% 15.24/2.50      ( ~ v1_funct_2(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
% 15.24/2.50      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 15.24/2.50      | k1_xboole_0 != sK2(k1_xboole_0,k1_xboole_0)
% 15.24/2.50      | k1_xboole_0 != k1_xboole_0 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_6675]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6676,plain,
% 15.24/2.50      ( X0 != X1
% 15.24/2.50      | X2 != X3
% 15.24/2.50      | X4 != sK2(X1,X3)
% 15.24/2.50      | v1_funct_2(X4,X0,X2) = iProver_top
% 15.24/2.50      | v1_funct_2(sK2(X1,X3),X1,X3) != iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_6675]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6678,plain,
% 15.24/2.50      ( k1_xboole_0 != sK2(k1_xboole_0,k1_xboole_0)
% 15.24/2.50      | k1_xboole_0 != k1_xboole_0
% 15.24/2.50      | v1_funct_2(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 15.24/2.50      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_6676]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_24,plain,
% 15.24/2.50      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 15.24/2.50      inference(cnf_transformation,[],[f90]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3474,plain,
% 15.24/2.50      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6971,plain,
% 15.24/2.50      ( v1_xboole_0(X0) != iProver_top
% 15.24/2.50      | v1_xboole_0(sK2(X1,X0)) = iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_3474,c_3477]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6981,plain,
% 15.24/2.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2(X1,X0)) ),
% 15.24/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_6971]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6983,plain,
% 15.24/2.50      ( v1_xboole_0(sK2(k1_xboole_0,k1_xboole_0))
% 15.24/2.50      | ~ v1_xboole_0(k1_xboole_0) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_6981]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3996,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
% 15.24/2.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | v1_funct_1(sK6) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_3464,c_3453]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_3997,plain,
% 15.24/2.50      ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 15.24/2.50      | ~ v1_funct_1(sK6)
% 15.24/2.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
% 15.24/2.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 15.24/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_3996]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4619,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
% 15.24/2.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_3996,c_39,c_38,c_3997]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4626,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) = iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_4619,c_3463]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4621,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 15.24/2.50      | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))) = k1_xboole_0
% 15.24/2.50      | u1_struct_0(sK3) = k1_relat_1(sK6) ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_4101,c_4619]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_5065,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))) = k1_xboole_0
% 15.24/2.50      | u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK4)))) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_4621,c_4942]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4945,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0))) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_4101,c_4942]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4946,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_4945,c_7]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_5260,plain,
% 15.24/2.50      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 15.24/2.50      | u1_struct_0(sK3) = k1_relat_1(sK6) ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_5065,c_4109,c_4946]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_5261,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top ),
% 15.24/2.50      inference(renaming,[status(thm)],[c_5260]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_5265,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_4101,c_5261]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_5380,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 15.24/2.50      | u1_struct_0(sK3) = k1_relat_1(sK6) ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_4626,c_5265]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6211,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 15.24/2.50      | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(sK4)) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_5380,c_5261]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_29006,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
% 15.24/2.50      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK4)) != iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_28859,c_6211]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_31675,plain,
% 15.24/2.50      ( ~ v1_xboole_0(sK2(X0,X1)) | k1_xboole_0 = sK2(X0,X1) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_6]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_31677,plain,
% 15.24/2.50      ( ~ v1_xboole_0(sK2(k1_xboole_0,k1_xboole_0))
% 15.24/2.50      | k1_xboole_0 = sK2(k1_xboole_0,k1_xboole_0) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_31675]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48295,plain,
% 15.24/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.24/2.50      | v1_funct_2(X3,k1_relat_1(X4),u1_struct_0(sK4))
% 15.24/2.50      | X3 != X0
% 15.24/2.50      | u1_struct_0(sK4) != X2
% 15.24/2.50      | k1_relat_1(X4) != X1 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_2618]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48297,plain,
% 15.24/2.50      ( X0 != X1
% 15.24/2.50      | u1_struct_0(sK4) != X2
% 15.24/2.50      | k1_relat_1(X3) != X4
% 15.24/2.50      | v1_funct_2(X1,X4,X2) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,k1_relat_1(X3),u1_struct_0(sK4)) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_48295]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48299,plain,
% 15.24/2.50      ( u1_struct_0(sK4) != k1_xboole_0
% 15.24/2.50      | k1_relat_1(k1_xboole_0) != k1_xboole_0
% 15.24/2.50      | k1_xboole_0 != k1_xboole_0
% 15.24/2.50      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK4)) = iProver_top
% 15.24/2.50      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_48297]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48311,plain,
% 15.24/2.50      ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0) ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_48129,c_39,c_99,c_100,c_127,c_128,c_5,c_3515,c_3523,
% 15.24/2.50                 c_3674,c_4808,c_6677,c_6678,c_6983,c_23506,c_28791,
% 15.24/2.50                 c_29006,c_29130,c_31677,c_48299]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_29133,plain,
% 15.24/2.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_28859,c_3464]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48351,plain,
% 15.24/2.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_48311,c_29133]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_29124,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
% 15.24/2.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0) ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_28859,c_4619]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6643,plain,
% 15.24/2.50      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 15.24/2.50      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.24/2.50      | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))) != iProver_top
% 15.24/2.50      | v2_pre_topc(X1) != iProver_top
% 15.24/2.50      | v2_pre_topc(X2) != iProver_top
% 15.24/2.50      | l1_pre_topc(X1) != iProver_top
% 15.24/2.50      | l1_pre_topc(X2) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_3479,c_3469]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_44485,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0)
% 15.24/2.50      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),X1) = iProver_top
% 15.24/2.50      | v5_pre_topc(X0,sK4,X1) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(X1)) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) != iProver_top
% 15.24/2.50      | r1_tarski(X0,k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1))) != iProver_top
% 15.24/2.50      | v2_pre_topc(X1) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK4) != iProver_top
% 15.24/2.50      | l1_pre_topc(X1) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK4) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_29124,c_6643]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_44494,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0)
% 15.24/2.50      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),X1) = iProver_top
% 15.24/2.50      | v5_pre_topc(X0,sK4,X1) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(X1)) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) != iProver_top
% 15.24/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) != iProver_top
% 15.24/2.50      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 15.24/2.50      | v2_pre_topc(X1) != iProver_top
% 15.24/2.50      | v2_pre_topc(sK4) != iProver_top
% 15.24/2.50      | l1_pre_topc(X1) != iProver_top
% 15.24/2.50      | l1_pre_topc(sK4) != iProver_top
% 15.24/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_44485,c_8]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6646,plain,
% 15.24/2.50      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_3479,c_5973]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6731,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_4619,c_6646]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_6733,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | r1_tarski(sK6,k1_xboole_0) != iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_6731,c_7]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4625,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0))) = iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_4619,c_3464]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_4627,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_4625,c_7]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_5977,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0))) != iProver_top ),
% 15.24/2.50      inference(superposition,[status(thm)],[c_4619,c_5973]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_5979,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_5977,c_7]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_7247,plain,
% 15.24/2.50      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6) ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_6733,c_4627,c_5979]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_7248,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 15.24/2.50      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
% 15.24/2.50      inference(renaming,[status(thm)],[c_7247]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_29095,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0)
% 15.24/2.50      | v1_funct_2(k1_xboole_0,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_28859,c_7248]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_44900,plain,
% 15.24/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.24/2.50      | v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 15.24/2.50      | X3 != X0
% 15.24/2.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X2
% 15.24/2.50      | u1_struct_0(sK3) != X1 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_2618]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_44902,plain,
% 15.24/2.50      ( X0 != X1
% 15.24/2.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != X2
% 15.24/2.50      | u1_struct_0(sK3) != X3
% 15.24/2.50      | v1_funct_2(X1,X3,X2) != iProver_top
% 15.24/2.50      | v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 15.24/2.50      inference(predicate_to_equality,[status(thm)],[c_44900]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_44904,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_xboole_0
% 15.24/2.50      | u1_struct_0(sK3) != k1_xboole_0
% 15.24/2.50      | k1_xboole_0 != k1_xboole_0
% 15.24/2.50      | v1_funct_2(k1_xboole_0,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top
% 15.24/2.50      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_44902]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_44597,plain,
% 15.24/2.50      ( X0 != X1 | u1_struct_0(sK3) != X1 | u1_struct_0(sK3) = X0 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_2612]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_46911,plain,
% 15.24/2.50      ( X0 != k1_relat_1(X1)
% 15.24/2.50      | u1_struct_0(sK3) = X0
% 15.24/2.50      | u1_struct_0(sK3) != k1_relat_1(X1) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_44597]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_46917,plain,
% 15.24/2.50      ( u1_struct_0(sK3) != k1_relat_1(k1_xboole_0)
% 15.24/2.50      | u1_struct_0(sK3) = k1_xboole_0
% 15.24/2.50      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_46911]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48276,plain,
% 15.24/2.50      ( X0 != X1 | X0 = k1_relat_1(X2) | k1_relat_1(X2) != X1 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_2612]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48278,plain,
% 15.24/2.50      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 15.24/2.50      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 15.24/2.50      | k1_xboole_0 != k1_xboole_0 ),
% 15.24/2.50      inference(instantiation,[status(thm)],[c_48276]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48678,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0) ),
% 15.24/2.50      inference(global_propositional_subsumption,
% 15.24/2.50                [status(thm)],
% 15.24/2.50                [c_44494,c_39,c_99,c_100,c_127,c_128,c_5,c_3515,c_3523,
% 15.24/2.50                 c_3674,c_4808,c_6677,c_6678,c_6983,c_23506,c_28791,
% 15.24/2.50                 c_29006,c_29095,c_29124,c_29130,c_31677,c_44904,c_46917,
% 15.24/2.50                 c_48278,c_48299]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48680,plain,
% 15.24/2.50      ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0) ),
% 15.24/2.50      inference(light_normalisation,[status(thm)],[c_48678,c_48311]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_49062,plain,
% 15.24/2.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 15.24/2.50      inference(light_normalisation,[status(thm)],[c_48351,c_48680]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_29134,plain,
% 15.24/2.50      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_28859,c_3463]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48352,plain,
% 15.24/2.50      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_48311,c_29134]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48963,plain,
% 15.24/2.50      ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 15.24/2.50      inference(light_normalisation,[status(thm)],[c_48352,c_48680]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_29115,plain,
% 15.24/2.50      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_28859,c_5973]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(c_48344,plain,
% 15.24/2.50      ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 15.24/2.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 15.24/2.50      inference(demodulation,[status(thm)],[c_48311,c_29115]) ).
% 15.24/2.50  
% 15.24/2.50  cnf(contradiction,plain,
% 15.24/2.50      ( $false ),
% 15.24/2.50      inference(minisat,[status(thm)],[c_49062,c_48963,c_48344]) ).
% 15.24/2.50  
% 15.24/2.50  
% 15.24/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.24/2.50  
% 15.24/2.50  ------                               Statistics
% 15.24/2.50  
% 15.24/2.50  ------ General
% 15.24/2.50  
% 15.24/2.50  abstr_ref_over_cycles:                  0
% 15.24/2.50  abstr_ref_under_cycles:                 0
% 15.24/2.50  gc_basic_clause_elim:                   0
% 15.24/2.50  forced_gc_time:                         0
% 15.24/2.50  parsing_time:                           0.017
% 15.24/2.50  unif_index_cands_time:                  0.
% 15.24/2.50  unif_index_add_time:                    0.
% 15.24/2.50  orderings_time:                         0.
% 15.24/2.50  out_proof_time:                         0.028
% 15.24/2.50  total_time:                             1.95
% 15.24/2.50  num_of_symbols:                         58
% 15.24/2.50  num_of_terms:                           36178
% 15.24/2.50  
% 15.24/2.50  ------ Preprocessing
% 15.24/2.50  
% 15.24/2.50  num_of_splits:                          0
% 15.24/2.50  num_of_split_atoms:                     0
% 15.24/2.50  num_of_reused_defs:                     0
% 15.24/2.50  num_eq_ax_congr_red:                    31
% 15.24/2.50  num_of_sem_filtered_clauses:            1
% 15.24/2.50  num_of_subtypes:                        0
% 15.24/2.50  monotx_restored_types:                  0
% 15.24/2.50  sat_num_of_epr_types:                   0
% 15.24/2.50  sat_num_of_non_cyclic_types:            0
% 15.24/2.50  sat_guarded_non_collapsed_types:        0
% 15.24/2.50  num_pure_diseq_elim:                    0
% 15.24/2.50  simp_replaced_by:                       0
% 15.24/2.50  res_preprocessed:                       201
% 15.24/2.50  prep_upred:                             0
% 15.24/2.50  prep_unflattend:                        47
% 15.24/2.50  smt_new_axioms:                         0
% 15.24/2.50  pred_elim_cands:                        9
% 15.24/2.50  pred_elim:                              3
% 15.24/2.50  pred_elim_cl:                           6
% 15.24/2.50  pred_elim_cycles:                       9
% 15.24/2.50  merged_defs:                            16
% 15.24/2.50  merged_defs_ncl:                        0
% 15.24/2.50  bin_hyper_res:                          17
% 15.24/2.50  prep_cycles:                            4
% 15.24/2.50  pred_elim_time:                         0.051
% 15.24/2.50  splitting_time:                         0.
% 15.24/2.50  sem_filter_time:                        0.
% 15.24/2.50  monotx_time:                            0.001
% 15.24/2.50  subtype_inf_time:                       0.
% 15.24/2.50  
% 15.24/2.50  ------ Problem properties
% 15.24/2.50  
% 15.24/2.50  clauses:                                41
% 15.24/2.50  conjectures:                            13
% 15.24/2.50  epr:                                    12
% 15.24/2.50  horn:                                   36
% 15.24/2.50  ground:                                 14
% 15.24/2.50  unary:                                  19
% 15.24/2.50  binary:                                 11
% 15.24/2.50  lits:                                   109
% 15.24/2.50  lits_eq:                                11
% 15.24/2.50  fd_pure:                                0
% 15.24/2.50  fd_pseudo:                              0
% 15.24/2.50  fd_cond:                                2
% 15.24/2.50  fd_pseudo_cond:                         1
% 15.24/2.50  ac_symbols:                             0
% 15.24/2.50  
% 15.24/2.50  ------ Propositional Solver
% 15.24/2.50  
% 15.24/2.50  prop_solver_calls:                      43
% 15.24/2.50  prop_fast_solver_calls:                 9470
% 15.24/2.50  smt_solver_calls:                       0
% 15.24/2.50  smt_fast_solver_calls:                  0
% 15.24/2.50  prop_num_of_clauses:                    19056
% 15.24/2.50  prop_preprocess_simplified:             29043
% 15.24/2.50  prop_fo_subsumed:                       675
% 15.24/2.50  prop_solver_time:                       0.
% 15.24/2.50  smt_solver_time:                        0.
% 15.24/2.50  smt_fast_solver_time:                   0.
% 15.24/2.50  prop_fast_solver_time:                  0.
% 15.24/2.50  prop_unsat_core_time:                   0.002
% 15.24/2.50  
% 15.24/2.50  ------ QBF
% 15.24/2.50  
% 15.24/2.50  qbf_q_res:                              0
% 15.24/2.50  qbf_num_tautologies:                    0
% 15.24/2.50  qbf_prep_cycles:                        0
% 15.24/2.50  
% 15.24/2.50  ------ BMC1
% 15.24/2.50  
% 15.24/2.50  bmc1_current_bound:                     -1
% 15.24/2.50  bmc1_last_solved_bound:                 -1
% 15.24/2.50  bmc1_unsat_core_size:                   -1
% 15.24/2.50  bmc1_unsat_core_parents_size:           -1
% 15.24/2.50  bmc1_merge_next_fun:                    0
% 15.24/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.24/2.50  
% 15.24/2.50  ------ Instantiation
% 15.24/2.50  
% 15.24/2.50  inst_num_of_clauses:                    705
% 15.24/2.50  inst_num_in_passive:                    187
% 15.24/2.50  inst_num_in_active:                     2713
% 15.24/2.50  inst_num_in_unprocessed:                203
% 15.24/2.50  inst_num_of_loops:                      3319
% 15.24/2.50  inst_num_of_learning_restarts:          1
% 15.24/2.50  inst_num_moves_active_passive:          595
% 15.24/2.50  inst_lit_activity:                      0
% 15.24/2.50  inst_lit_activity_moves:                0
% 15.24/2.50  inst_num_tautologies:                   0
% 15.24/2.50  inst_num_prop_implied:                  0
% 15.24/2.50  inst_num_existing_simplified:           0
% 15.24/2.50  inst_num_eq_res_simplified:             0
% 15.24/2.50  inst_num_child_elim:                    0
% 15.24/2.50  inst_num_of_dismatching_blockings:      1746
% 15.24/2.50  inst_num_of_non_proper_insts:           5355
% 15.24/2.50  inst_num_of_duplicates:                 0
% 15.24/2.50  inst_inst_num_from_inst_to_res:         0
% 15.24/2.50  inst_dismatching_checking_time:         0.
% 15.24/2.50  
% 15.24/2.50  ------ Resolution
% 15.24/2.50  
% 15.24/2.50  res_num_of_clauses:                     56
% 15.24/2.50  res_num_in_passive:                     56
% 15.24/2.50  res_num_in_active:                      0
% 15.24/2.50  res_num_of_loops:                       205
% 15.24/2.50  res_forward_subset_subsumed:            323
% 15.24/2.50  res_backward_subset_subsumed:           12
% 15.24/2.50  res_forward_subsumed:                   2
% 15.24/2.50  res_backward_subsumed:                  0
% 15.24/2.50  res_forward_subsumption_resolution:     3
% 15.24/2.50  res_backward_subsumption_resolution:    0
% 15.24/2.50  res_clause_to_clause_subsumption:       5850
% 15.24/2.50  res_orphan_elimination:                 0
% 15.24/2.50  res_tautology_del:                      478
% 15.24/2.50  res_num_eq_res_simplified:              0
% 15.24/2.50  res_num_sel_changes:                    0
% 15.24/2.50  res_moves_from_active_to_pass:          0
% 15.24/2.50  
% 15.24/2.50  ------ Superposition
% 15.24/2.50  
% 15.24/2.50  sup_time_total:                         0.
% 15.24/2.50  sup_time_generating:                    0.
% 15.24/2.50  sup_time_sim_full:                      0.
% 15.24/2.50  sup_time_sim_immed:                     0.
% 15.24/2.50  
% 15.24/2.50  sup_num_of_clauses:                     766
% 15.24/2.50  sup_num_in_active:                      60
% 15.24/2.50  sup_num_in_passive:                     706
% 15.24/2.50  sup_num_of_loops:                       662
% 15.24/2.50  sup_fw_superposition:                   2804
% 15.24/2.50  sup_bw_superposition:                   862
% 15.24/2.50  sup_immediate_simplified:               1335
% 15.24/2.50  sup_given_eliminated:                   45
% 15.24/2.50  comparisons_done:                       0
% 15.24/2.50  comparisons_avoided:                    34
% 15.24/2.50  
% 15.24/2.50  ------ Simplifications
% 15.24/2.50  
% 15.24/2.50  
% 15.24/2.50  sim_fw_subset_subsumed:                 933
% 15.24/2.50  sim_bw_subset_subsumed:                 598
% 15.24/2.50  sim_fw_subsumed:                        82
% 15.24/2.50  sim_bw_subsumed:                        153
% 15.24/2.50  sim_fw_subsumption_res:                 0
% 15.24/2.50  sim_bw_subsumption_res:                 0
% 15.24/2.50  sim_tautology_del:                      210
% 15.24/2.50  sim_eq_tautology_del:                   17
% 15.24/2.50  sim_eq_res_simp:                        0
% 15.24/2.50  sim_fw_demodulated:                     315
% 15.24/2.50  sim_bw_demodulated:                     320
% 15.24/2.50  sim_light_normalised:                   129
% 15.24/2.50  sim_joinable_taut:                      0
% 15.24/2.50  sim_joinable_simp:                      0
% 15.24/2.50  sim_ac_normalised:                      0
% 15.24/2.50  sim_smt_subsumption:                    0
% 15.24/2.50  
%------------------------------------------------------------------------------
