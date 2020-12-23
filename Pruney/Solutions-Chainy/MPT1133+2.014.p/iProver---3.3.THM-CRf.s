%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:50 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  188 (3810 expanded)
%              Number of clauses        :  115 ( 796 expanded)
%              Number of leaves         :   16 (1169 expanded)
%              Depth                    :   21
%              Number of atoms          :  981 (46421 expanded)
%              Number of equality atoms :  279 (4471 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,conjecture,(
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

fof(f30,negated_conjecture,(
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
    inference(negated_conjecture,[],[f29])).

fof(f64,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f79,plain,(
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
    inference(nnf_transformation,[],[f65])).

fof(f80,plain,(
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
    inference(flattening,[],[f79])).

fof(f84,plain,(
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
     => ( ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK5 = X2
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
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
              | ~ v5_pre_topc(sK4,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK4,X0,X1) )
            & sK4 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
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
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
                  | ~ v5_pre_topc(X2,X0,sK3) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
                  | v5_pre_topc(X2,X0,sK3) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK2,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK2,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,
    ( ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ v5_pre_topc(sK4,sK2,sK3) )
    & ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | v5_pre_topc(sK4,sK2,sK3) )
    & sK4 = sK5
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f80,f84,f83,f82,f81])).

fof(f147,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f85])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f145,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f85])).

fof(f146,plain,(
    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f85])).

fof(f144,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f85])).

fof(f148,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f85])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f43])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f149,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f85])).

fof(f28,axiom,(
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

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f78,plain,(
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
    inference(nnf_transformation,[],[f63])).

fof(f137,plain,(
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
    inference(cnf_transformation,[],[f78])).

fof(f159,plain,(
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
    inference(equality_resolution,[],[f137])).

fof(f138,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f85])).

fof(f139,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f85])).

fof(f140,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f85])).

fof(f141,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f85])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f133,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f131,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f132,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f136,plain,(
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
    inference(cnf_transformation,[],[f78])).

fof(f160,plain,(
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
    inference(equality_resolution,[],[f136])).

fof(f150,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f85])).

fof(f143,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f85])).

fof(f27,axiom,(
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

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f77,plain,(
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
    inference(nnf_transformation,[],[f61])).

fof(f135,plain,(
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
    inference(cnf_transformation,[],[f77])).

fof(f157,plain,(
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
    inference(equality_resolution,[],[f135])).

fof(f134,plain,(
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
    inference(cnf_transformation,[],[f77])).

fof(f158,plain,(
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
    inference(equality_resolution,[],[f134])).

cnf(c_55,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_5641,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_41,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_5653,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_partfun1(X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_10951,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5641,c_5653])).

cnf(c_57,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_72,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_56,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_73,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_58,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_5638,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_54,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f148])).

cnf(c_5681,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5638,c_54])).

cnf(c_21,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_15,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_751,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_21,c_15])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_755,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_751,c_20])).

cnf(c_756,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_755])).

cnf(c_5631,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_6728,plain,
    ( r1_tarski(k2_relat_1(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5681,c_5631])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_5664,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_9773,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5641,c_5664])).

cnf(c_28,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_5663,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10385,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0) = iProver_top
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9773,c_5663])).

cnf(c_10637,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10385,c_72])).

cnf(c_10638,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0) = iProver_top
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10637])).

cnf(c_53,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_5642,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_5682,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5642,c_54])).

cnf(c_50,plain,
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
    inference(cnf_transformation,[],[f159])).

cnf(c_5645,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_7715,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5641,c_5645])).

cnf(c_64,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_65,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_63,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_66,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_62,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_67,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_61,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_68,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_47,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_5826,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_5827,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5826])).

cnf(c_45,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_6084,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_6085,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6084])).

cnf(c_46,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_6336,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_6337,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6336])).

cnf(c_51,plain,
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
    inference(cnf_transformation,[],[f160])).

cnf(c_5644,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_7323,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5641,c_5644])).

cnf(c_52,negated_conjecture,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_5643,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_5683,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5643,c_54])).

cnf(c_59,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_5637,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_5680,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5637,c_54])).

cnf(c_48,plain,
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
    inference(cnf_transformation,[],[f157])).

cnf(c_6004,plain,
    ( v5_pre_topc(sK5,X0,sK3)
    | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_6652,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_6004])).

cnf(c_6653,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
    | v5_pre_topc(sK5,sK2,sK3) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6652])).

cnf(c_7433,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7323,c_65,c_66,c_67,c_68,c_72,c_73,c_5683,c_5680,c_5681,c_5827,c_6085,c_6337,c_6653])).

cnf(c_7434,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7433])).

cnf(c_8016,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7715,c_65,c_66,c_67,c_68,c_72,c_73,c_5683,c_5680,c_5681,c_5827,c_6085,c_6337,c_6653,c_7323])).

cnf(c_8017,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8016])).

cnf(c_8020,plain,
    ( v5_pre_topc(sK5,sK2,sK3) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5682,c_8017])).

cnf(c_49,plain,
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
    inference(cnf_transformation,[],[f158])).

cnf(c_6554,plain,
    ( ~ v5_pre_topc(sK5,X0,sK3)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_8126,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | ~ v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_6554])).

cnf(c_8127,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
    | v5_pre_topc(sK5,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8126])).

cnf(c_8147,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8020,c_65,c_66,c_67,c_68,c_72,c_5680,c_5681,c_7434,c_8127])).

cnf(c_10010,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k2_relat_1(sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9773,c_8147])).

cnf(c_10167,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10010,c_6728])).

cnf(c_10643,plain,
    ( v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10638,c_10167])).

cnf(c_11878,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10951,c_72,c_73,c_6728,c_10643])).

cnf(c_10953,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_partfun1(sK5,u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5681,c_5653])).

cnf(c_6726,plain,
    ( r1_tarski(k2_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5641,c_5631])).

cnf(c_9775,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5681,c_5664])).

cnf(c_10386,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),X0) = iProver_top
    | v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9775,c_5663])).

cnf(c_10628,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10386,c_72])).

cnf(c_10629,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),X0) = iProver_top
    | v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10628])).

cnf(c_5646,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_8170,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5641,c_5646])).

cnf(c_74,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_5841,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_5842,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5841])).

cnf(c_6094,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_6095,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6094])).

cnf(c_6347,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_6348,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6347])).

cnf(c_6005,plain,
    ( ~ v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,X0,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_6625,plain,
    ( ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_6005])).

cnf(c_6626,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,sK2,sK3) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6625])).

cnf(c_7029,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_7030,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7029])).

cnf(c_6292,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)
    | v5_pre_topc(sK5,sK2,X0)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X0))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X0))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_7166,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_6292])).

cnf(c_7167,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7166])).

cnf(c_8654,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8170,c_65,c_66,c_67,c_68,c_72,c_73,c_74,c_5683,c_5680,c_5681,c_5682,c_5842,c_6095,c_6348,c_6626,c_7030,c_7167])).

cnf(c_8655,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8654])).

cnf(c_8658,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8655,c_65,c_66,c_67,c_68,c_72,c_73,c_74,c_5680,c_5681,c_5682,c_5842,c_6095,c_6348,c_7030,c_7167])).

cnf(c_9878,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9775,c_8658])).

cnf(c_10242,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9878,c_6726])).

cnf(c_10634,plain,
    ( v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k2_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10629,c_10242])).

cnf(c_11330,plain,
    ( u1_struct_0(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10953,c_72,c_5680,c_6726,c_10634])).

cnf(c_11880,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11878,c_11330])).

cnf(c_5640,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_11347,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11330,c_5640])).

cnf(c_11882,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11880,c_11347])).

cnf(c_11333,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11330,c_10167])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11882,c_11333])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.36/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.36/1.05  
% 0.36/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.36/1.05  
% 0.36/1.05  ------  iProver source info
% 0.36/1.05  
% 0.36/1.05  git: date: 2020-06-30 10:37:57 +0100
% 0.36/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.36/1.05  git: non_committed_changes: false
% 0.36/1.05  git: last_make_outside_of_git: false
% 0.36/1.05  
% 0.36/1.05  ------ 
% 0.36/1.05  
% 0.36/1.05  ------ Input Options
% 0.36/1.05  
% 0.36/1.05  --out_options                           all
% 0.36/1.05  --tptp_safe_out                         true
% 0.36/1.05  --problem_path                          ""
% 0.36/1.05  --include_path                          ""
% 0.36/1.05  --clausifier                            res/vclausify_rel
% 0.36/1.05  --clausifier_options                    ""
% 0.36/1.05  --stdin                                 false
% 0.36/1.05  --stats_out                             all
% 0.36/1.05  
% 0.36/1.05  ------ General Options
% 0.36/1.05  
% 0.36/1.05  --fof                                   false
% 0.36/1.05  --time_out_real                         305.
% 0.36/1.05  --time_out_virtual                      -1.
% 0.36/1.05  --symbol_type_check                     false
% 0.36/1.05  --clausify_out                          false
% 0.36/1.05  --sig_cnt_out                           false
% 0.36/1.05  --trig_cnt_out                          false
% 0.36/1.05  --trig_cnt_out_tolerance                1.
% 0.36/1.05  --trig_cnt_out_sk_spl                   false
% 0.36/1.05  --abstr_cl_out                          false
% 0.36/1.05  
% 0.36/1.05  ------ Global Options
% 0.36/1.05  
% 0.36/1.05  --schedule                              default
% 0.36/1.05  --add_important_lit                     false
% 0.36/1.05  --prop_solver_per_cl                    1000
% 0.36/1.05  --min_unsat_core                        false
% 0.36/1.05  --soft_assumptions                      false
% 0.36/1.05  --soft_lemma_size                       3
% 0.36/1.05  --prop_impl_unit_size                   0
% 0.36/1.05  --prop_impl_unit                        []
% 0.36/1.05  --share_sel_clauses                     true
% 0.36/1.05  --reset_solvers                         false
% 0.36/1.05  --bc_imp_inh                            [conj_cone]
% 0.36/1.05  --conj_cone_tolerance                   3.
% 0.36/1.05  --extra_neg_conj                        none
% 0.36/1.05  --large_theory_mode                     true
% 0.36/1.05  --prolific_symb_bound                   200
% 0.36/1.05  --lt_threshold                          2000
% 0.36/1.05  --clause_weak_htbl                      true
% 0.36/1.05  --gc_record_bc_elim                     false
% 0.36/1.05  
% 0.36/1.05  ------ Preprocessing Options
% 0.36/1.05  
% 0.36/1.05  --preprocessing_flag                    true
% 0.36/1.05  --time_out_prep_mult                    0.1
% 0.36/1.05  --splitting_mode                        input
% 0.36/1.05  --splitting_grd                         true
% 0.36/1.05  --splitting_cvd                         false
% 0.36/1.05  --splitting_cvd_svl                     false
% 0.36/1.05  --splitting_nvd                         32
% 0.36/1.05  --sub_typing                            true
% 0.36/1.05  --prep_gs_sim                           true
% 0.36/1.05  --prep_unflatten                        true
% 0.36/1.05  --prep_res_sim                          true
% 0.36/1.05  --prep_upred                            true
% 0.36/1.05  --prep_sem_filter                       exhaustive
% 0.36/1.05  --prep_sem_filter_out                   false
% 0.36/1.05  --pred_elim                             true
% 0.36/1.05  --res_sim_input                         true
% 0.36/1.05  --eq_ax_congr_red                       true
% 0.36/1.05  --pure_diseq_elim                       true
% 0.36/1.05  --brand_transform                       false
% 0.36/1.05  --non_eq_to_eq                          false
% 0.36/1.05  --prep_def_merge                        true
% 0.36/1.05  --prep_def_merge_prop_impl              false
% 0.36/1.05  --prep_def_merge_mbd                    true
% 0.36/1.05  --prep_def_merge_tr_red                 false
% 0.36/1.05  --prep_def_merge_tr_cl                  false
% 0.36/1.05  --smt_preprocessing                     true
% 0.36/1.05  --smt_ac_axioms                         fast
% 0.36/1.05  --preprocessed_out                      false
% 0.36/1.05  --preprocessed_stats                    false
% 0.36/1.05  
% 0.36/1.05  ------ Abstraction refinement Options
% 0.36/1.05  
% 0.36/1.05  --abstr_ref                             []
% 0.36/1.05  --abstr_ref_prep                        false
% 0.36/1.05  --abstr_ref_until_sat                   false
% 0.36/1.05  --abstr_ref_sig_restrict                funpre
% 0.36/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.36/1.05  --abstr_ref_under                       []
% 0.36/1.05  
% 0.36/1.05  ------ SAT Options
% 0.36/1.05  
% 0.36/1.05  --sat_mode                              false
% 0.36/1.05  --sat_fm_restart_options                ""
% 0.36/1.05  --sat_gr_def                            false
% 0.36/1.05  --sat_epr_types                         true
% 0.36/1.05  --sat_non_cyclic_types                  false
% 0.36/1.05  --sat_finite_models                     false
% 0.36/1.05  --sat_fm_lemmas                         false
% 0.36/1.05  --sat_fm_prep                           false
% 0.36/1.05  --sat_fm_uc_incr                        true
% 0.36/1.05  --sat_out_model                         small
% 0.36/1.05  --sat_out_clauses                       false
% 0.36/1.05  
% 0.36/1.05  ------ QBF Options
% 0.36/1.05  
% 0.36/1.05  --qbf_mode                              false
% 0.36/1.05  --qbf_elim_univ                         false
% 0.36/1.05  --qbf_dom_inst                          none
% 0.36/1.05  --qbf_dom_pre_inst                      false
% 0.36/1.05  --qbf_sk_in                             false
% 0.36/1.05  --qbf_pred_elim                         true
% 0.36/1.05  --qbf_split                             512
% 0.36/1.05  
% 0.36/1.05  ------ BMC1 Options
% 0.36/1.05  
% 0.36/1.05  --bmc1_incremental                      false
% 0.36/1.05  --bmc1_axioms                           reachable_all
% 0.36/1.05  --bmc1_min_bound                        0
% 0.36/1.05  --bmc1_max_bound                        -1
% 0.36/1.05  --bmc1_max_bound_default                -1
% 0.36/1.05  --bmc1_symbol_reachability              true
% 0.36/1.05  --bmc1_property_lemmas                  false
% 0.36/1.05  --bmc1_k_induction                      false
% 0.36/1.05  --bmc1_non_equiv_states                 false
% 0.36/1.05  --bmc1_deadlock                         false
% 0.36/1.05  --bmc1_ucm                              false
% 0.36/1.05  --bmc1_add_unsat_core                   none
% 0.36/1.05  --bmc1_unsat_core_children              false
% 0.36/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.36/1.05  --bmc1_out_stat                         full
% 0.36/1.05  --bmc1_ground_init                      false
% 0.36/1.05  --bmc1_pre_inst_next_state              false
% 0.36/1.05  --bmc1_pre_inst_state                   false
% 0.36/1.05  --bmc1_pre_inst_reach_state             false
% 0.36/1.05  --bmc1_out_unsat_core                   false
% 0.36/1.05  --bmc1_aig_witness_out                  false
% 0.36/1.05  --bmc1_verbose                          false
% 0.36/1.05  --bmc1_dump_clauses_tptp                false
% 0.36/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.36/1.05  --bmc1_dump_file                        -
% 0.36/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.36/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.36/1.05  --bmc1_ucm_extend_mode                  1
% 0.36/1.05  --bmc1_ucm_init_mode                    2
% 0.36/1.05  --bmc1_ucm_cone_mode                    none
% 0.36/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.36/1.05  --bmc1_ucm_relax_model                  4
% 0.36/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.36/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.36/1.05  --bmc1_ucm_layered_model                none
% 0.36/1.05  --bmc1_ucm_max_lemma_size               10
% 0.36/1.05  
% 0.36/1.05  ------ AIG Options
% 0.36/1.05  
% 0.36/1.05  --aig_mode                              false
% 0.36/1.05  
% 0.36/1.05  ------ Instantiation Options
% 0.36/1.05  
% 0.36/1.05  --instantiation_flag                    true
% 0.36/1.05  --inst_sos_flag                         true
% 0.36/1.05  --inst_sos_phase                        true
% 0.36/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.36/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.36/1.05  --inst_lit_sel_side                     num_symb
% 0.36/1.05  --inst_solver_per_active                1400
% 0.36/1.05  --inst_solver_calls_frac                1.
% 0.36/1.05  --inst_passive_queue_type               priority_queues
% 0.36/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.36/1.05  --inst_passive_queues_freq              [25;2]
% 0.36/1.05  --inst_dismatching                      true
% 0.36/1.05  --inst_eager_unprocessed_to_passive     true
% 0.36/1.05  --inst_prop_sim_given                   true
% 0.36/1.05  --inst_prop_sim_new                     false
% 0.36/1.05  --inst_subs_new                         false
% 0.36/1.05  --inst_eq_res_simp                      false
% 0.36/1.05  --inst_subs_given                       false
% 0.36/1.05  --inst_orphan_elimination               true
% 0.36/1.05  --inst_learning_loop_flag               true
% 0.36/1.05  --inst_learning_start                   3000
% 0.36/1.05  --inst_learning_factor                  2
% 0.36/1.05  --inst_start_prop_sim_after_learn       3
% 0.36/1.05  --inst_sel_renew                        solver
% 0.36/1.05  --inst_lit_activity_flag                true
% 0.36/1.05  --inst_restr_to_given                   false
% 0.36/1.05  --inst_activity_threshold               500
% 0.36/1.05  --inst_out_proof                        true
% 0.36/1.05  
% 0.36/1.05  ------ Resolution Options
% 0.36/1.05  
% 0.36/1.05  --resolution_flag                       true
% 0.36/1.05  --res_lit_sel                           adaptive
% 0.36/1.05  --res_lit_sel_side                      none
% 0.36/1.05  --res_ordering                          kbo
% 0.36/1.05  --res_to_prop_solver                    active
% 0.36/1.05  --res_prop_simpl_new                    false
% 0.36/1.05  --res_prop_simpl_given                  true
% 0.36/1.05  --res_passive_queue_type                priority_queues
% 0.36/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.36/1.05  --res_passive_queues_freq               [15;5]
% 0.36/1.05  --res_forward_subs                      full
% 0.36/1.05  --res_backward_subs                     full
% 0.36/1.05  --res_forward_subs_resolution           true
% 0.36/1.05  --res_backward_subs_resolution          true
% 0.36/1.05  --res_orphan_elimination                true
% 0.36/1.05  --res_time_limit                        2.
% 0.36/1.05  --res_out_proof                         true
% 0.36/1.05  
% 0.36/1.05  ------ Superposition Options
% 0.36/1.05  
% 0.36/1.05  --superposition_flag                    true
% 0.36/1.05  --sup_passive_queue_type                priority_queues
% 0.36/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.36/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.36/1.05  --demod_completeness_check              fast
% 0.36/1.05  --demod_use_ground                      true
% 0.36/1.05  --sup_to_prop_solver                    passive
% 0.36/1.05  --sup_prop_simpl_new                    true
% 0.36/1.05  --sup_prop_simpl_given                  true
% 0.36/1.05  --sup_fun_splitting                     true
% 0.36/1.05  --sup_smt_interval                      50000
% 0.36/1.05  
% 0.36/1.05  ------ Superposition Simplification Setup
% 0.36/1.05  
% 0.36/1.05  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 0.36/1.05  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 0.36/1.05  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 0.36/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.36/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 0.36/1.05  --sup_full_bw                           [BwDemod;BwSubsumption]
% 0.36/1.05  --sup_immed_triv                        [TrivRules]
% 0.36/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.05  --sup_immed_bw_main                     []
% 0.36/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 0.36/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.36/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.05  --sup_input_bw                          []
% 0.36/1.05  
% 0.36/1.05  ------ Combination Options
% 0.36/1.05  
% 0.36/1.05  --comb_res_mult                         3
% 0.36/1.05  --comb_sup_mult                         2
% 0.36/1.05  --comb_inst_mult                        10
% 0.36/1.05  
% 0.36/1.05  ------ Debug Options
% 0.36/1.05  
% 0.36/1.05  --dbg_backtrace                         false
% 0.36/1.05  --dbg_dump_prop_clauses                 false
% 0.36/1.05  --dbg_dump_prop_clauses_file            -
% 0.36/1.05  --dbg_out_stat                          false
% 0.36/1.05  ------ Parsing...
% 0.36/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.36/1.05  
% 0.36/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.36/1.05  
% 0.36/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.36/1.05  
% 0.36/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.36/1.05  ------ Proving...
% 0.36/1.05  ------ Problem Properties 
% 0.36/1.05  
% 0.36/1.05  
% 0.36/1.05  clauses                                 58
% 0.36/1.05  conjectures                             13
% 0.36/1.05  EPR                                     15
% 0.36/1.05  Horn                                    53
% 0.36/1.05  unary                                   26
% 0.36/1.05  binary                                  13
% 0.36/1.05  lits                                    150
% 0.36/1.05  lits eq                                 16
% 0.36/1.05  fd_pure                                 0
% 0.36/1.05  fd_pseudo                               0
% 0.36/1.05  fd_cond                                 7
% 0.36/1.05  fd_pseudo_cond                          2
% 0.36/1.05  AC symbols                              0
% 0.36/1.05  
% 0.36/1.05  ------ Schedule dynamic 5 is on 
% 0.36/1.05  
% 0.36/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.36/1.05  
% 0.36/1.05  
% 0.36/1.05  ------ 
% 0.36/1.05  Current options:
% 0.36/1.05  ------ 
% 0.36/1.05  
% 0.36/1.05  ------ Input Options
% 0.36/1.05  
% 0.36/1.05  --out_options                           all
% 0.36/1.05  --tptp_safe_out                         true
% 0.36/1.05  --problem_path                          ""
% 0.36/1.05  --include_path                          ""
% 0.36/1.05  --clausifier                            res/vclausify_rel
% 0.36/1.05  --clausifier_options                    ""
% 0.36/1.05  --stdin                                 false
% 0.36/1.05  --stats_out                             all
% 0.36/1.05  
% 0.36/1.05  ------ General Options
% 0.36/1.05  
% 0.36/1.05  --fof                                   false
% 0.36/1.05  --time_out_real                         305.
% 0.36/1.05  --time_out_virtual                      -1.
% 0.36/1.05  --symbol_type_check                     false
% 0.36/1.05  --clausify_out                          false
% 0.36/1.05  --sig_cnt_out                           false
% 0.36/1.05  --trig_cnt_out                          false
% 0.36/1.05  --trig_cnt_out_tolerance                1.
% 0.36/1.05  --trig_cnt_out_sk_spl                   false
% 0.36/1.05  --abstr_cl_out                          false
% 0.36/1.05  
% 0.36/1.05  ------ Global Options
% 0.36/1.05  
% 0.36/1.05  --schedule                              default
% 0.36/1.05  --add_important_lit                     false
% 0.36/1.05  --prop_solver_per_cl                    1000
% 0.36/1.05  --min_unsat_core                        false
% 0.36/1.05  --soft_assumptions                      false
% 0.36/1.05  --soft_lemma_size                       3
% 0.36/1.05  --prop_impl_unit_size                   0
% 0.36/1.05  --prop_impl_unit                        []
% 0.36/1.05  --share_sel_clauses                     true
% 0.36/1.05  --reset_solvers                         false
% 0.36/1.05  --bc_imp_inh                            [conj_cone]
% 0.36/1.05  --conj_cone_tolerance                   3.
% 0.36/1.05  --extra_neg_conj                        none
% 0.36/1.05  --large_theory_mode                     true
% 0.36/1.05  --prolific_symb_bound                   200
% 0.36/1.05  --lt_threshold                          2000
% 0.36/1.05  --clause_weak_htbl                      true
% 0.36/1.05  --gc_record_bc_elim                     false
% 0.36/1.05  
% 0.36/1.05  ------ Preprocessing Options
% 0.36/1.05  
% 0.36/1.05  --preprocessing_flag                    true
% 0.36/1.05  --time_out_prep_mult                    0.1
% 0.36/1.05  --splitting_mode                        input
% 0.36/1.05  --splitting_grd                         true
% 0.36/1.05  --splitting_cvd                         false
% 0.36/1.05  --splitting_cvd_svl                     false
% 0.36/1.05  --splitting_nvd                         32
% 0.36/1.05  --sub_typing                            true
% 0.36/1.05  --prep_gs_sim                           true
% 0.36/1.05  --prep_unflatten                        true
% 0.36/1.05  --prep_res_sim                          true
% 0.36/1.05  --prep_upred                            true
% 0.36/1.05  --prep_sem_filter                       exhaustive
% 0.36/1.05  --prep_sem_filter_out                   false
% 0.36/1.05  --pred_elim                             true
% 0.36/1.05  --res_sim_input                         true
% 0.36/1.05  --eq_ax_congr_red                       true
% 0.36/1.05  --pure_diseq_elim                       true
% 0.36/1.05  --brand_transform                       false
% 0.36/1.05  --non_eq_to_eq                          false
% 0.36/1.05  --prep_def_merge                        true
% 0.36/1.05  --prep_def_merge_prop_impl              false
% 0.36/1.05  --prep_def_merge_mbd                    true
% 0.36/1.05  --prep_def_merge_tr_red                 false
% 0.36/1.05  --prep_def_merge_tr_cl                  false
% 0.36/1.05  --smt_preprocessing                     true
% 0.36/1.05  --smt_ac_axioms                         fast
% 0.36/1.05  --preprocessed_out                      false
% 0.36/1.05  --preprocessed_stats                    false
% 0.36/1.05  
% 0.36/1.05  ------ Abstraction refinement Options
% 0.36/1.05  
% 0.36/1.05  --abstr_ref                             []
% 0.36/1.05  --abstr_ref_prep                        false
% 0.36/1.05  --abstr_ref_until_sat                   false
% 0.36/1.05  --abstr_ref_sig_restrict                funpre
% 0.36/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.36/1.05  --abstr_ref_under                       []
% 0.36/1.05  
% 0.36/1.05  ------ SAT Options
% 0.36/1.05  
% 0.36/1.05  --sat_mode                              false
% 0.36/1.05  --sat_fm_restart_options                ""
% 0.36/1.05  --sat_gr_def                            false
% 0.36/1.05  --sat_epr_types                         true
% 0.36/1.05  --sat_non_cyclic_types                  false
% 0.36/1.05  --sat_finite_models                     false
% 0.36/1.05  --sat_fm_lemmas                         false
% 0.36/1.05  --sat_fm_prep                           false
% 0.36/1.05  --sat_fm_uc_incr                        true
% 0.36/1.05  --sat_out_model                         small
% 0.36/1.05  --sat_out_clauses                       false
% 0.36/1.05  
% 0.36/1.05  ------ QBF Options
% 0.36/1.05  
% 0.36/1.05  --qbf_mode                              false
% 0.36/1.05  --qbf_elim_univ                         false
% 0.36/1.05  --qbf_dom_inst                          none
% 0.36/1.05  --qbf_dom_pre_inst                      false
% 0.36/1.05  --qbf_sk_in                             false
% 0.36/1.05  --qbf_pred_elim                         true
% 0.36/1.05  --qbf_split                             512
% 0.36/1.05  
% 0.36/1.05  ------ BMC1 Options
% 0.36/1.05  
% 0.36/1.05  --bmc1_incremental                      false
% 0.36/1.05  --bmc1_axioms                           reachable_all
% 0.36/1.05  --bmc1_min_bound                        0
% 0.36/1.05  --bmc1_max_bound                        -1
% 0.36/1.05  --bmc1_max_bound_default                -1
% 0.36/1.05  --bmc1_symbol_reachability              true
% 0.36/1.05  --bmc1_property_lemmas                  false
% 0.36/1.05  --bmc1_k_induction                      false
% 0.36/1.05  --bmc1_non_equiv_states                 false
% 0.36/1.05  --bmc1_deadlock                         false
% 0.36/1.05  --bmc1_ucm                              false
% 0.36/1.05  --bmc1_add_unsat_core                   none
% 0.36/1.05  --bmc1_unsat_core_children              false
% 0.36/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.36/1.05  --bmc1_out_stat                         full
% 0.36/1.05  --bmc1_ground_init                      false
% 0.36/1.05  --bmc1_pre_inst_next_state              false
% 0.36/1.05  --bmc1_pre_inst_state                   false
% 0.36/1.05  --bmc1_pre_inst_reach_state             false
% 0.36/1.05  --bmc1_out_unsat_core                   false
% 0.36/1.05  --bmc1_aig_witness_out                  false
% 0.36/1.05  --bmc1_verbose                          false
% 0.36/1.05  --bmc1_dump_clauses_tptp                false
% 0.36/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.36/1.05  --bmc1_dump_file                        -
% 0.36/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.36/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.36/1.05  --bmc1_ucm_extend_mode                  1
% 0.36/1.05  --bmc1_ucm_init_mode                    2
% 0.36/1.05  --bmc1_ucm_cone_mode                    none
% 0.36/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.36/1.05  --bmc1_ucm_relax_model                  4
% 0.36/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.36/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.36/1.05  --bmc1_ucm_layered_model                none
% 0.36/1.05  --bmc1_ucm_max_lemma_size               10
% 0.36/1.05  
% 0.36/1.05  ------ AIG Options
% 0.36/1.05  
% 0.36/1.05  --aig_mode                              false
% 0.36/1.05  
% 0.36/1.05  ------ Instantiation Options
% 0.36/1.05  
% 0.36/1.05  --instantiation_flag                    true
% 0.36/1.05  --inst_sos_flag                         true
% 0.36/1.05  --inst_sos_phase                        true
% 0.36/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.36/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.36/1.05  --inst_lit_sel_side                     none
% 0.36/1.05  --inst_solver_per_active                1400
% 0.36/1.05  --inst_solver_calls_frac                1.
% 0.36/1.05  --inst_passive_queue_type               priority_queues
% 0.36/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.36/1.05  --inst_passive_queues_freq              [25;2]
% 0.36/1.05  --inst_dismatching                      true
% 0.36/1.05  --inst_eager_unprocessed_to_passive     true
% 0.36/1.05  --inst_prop_sim_given                   true
% 0.36/1.05  --inst_prop_sim_new                     false
% 0.36/1.05  --inst_subs_new                         false
% 0.36/1.05  --inst_eq_res_simp                      false
% 0.36/1.05  --inst_subs_given                       false
% 0.36/1.05  --inst_orphan_elimination               true
% 0.36/1.05  --inst_learning_loop_flag               true
% 0.36/1.05  --inst_learning_start                   3000
% 0.36/1.05  --inst_learning_factor                  2
% 0.36/1.05  --inst_start_prop_sim_after_learn       3
% 0.36/1.05  --inst_sel_renew                        solver
% 0.36/1.05  --inst_lit_activity_flag                true
% 0.36/1.05  --inst_restr_to_given                   false
% 0.36/1.05  --inst_activity_threshold               500
% 0.36/1.05  --inst_out_proof                        true
% 0.36/1.05  
% 0.36/1.05  ------ Resolution Options
% 0.36/1.05  
% 0.36/1.05  --resolution_flag                       false
% 0.36/1.05  --res_lit_sel                           adaptive
% 0.36/1.05  --res_lit_sel_side                      none
% 0.36/1.05  --res_ordering                          kbo
% 0.36/1.05  --res_to_prop_solver                    active
% 0.36/1.05  --res_prop_simpl_new                    false
% 0.36/1.05  --res_prop_simpl_given                  true
% 0.36/1.05  --res_passive_queue_type                priority_queues
% 0.36/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.36/1.05  --res_passive_queues_freq               [15;5]
% 0.36/1.05  --res_forward_subs                      full
% 0.36/1.05  --res_backward_subs                     full
% 0.36/1.05  --res_forward_subs_resolution           true
% 0.36/1.05  --res_backward_subs_resolution          true
% 0.36/1.05  --res_orphan_elimination                true
% 0.36/1.05  --res_time_limit                        2.
% 0.36/1.05  --res_out_proof                         true
% 0.36/1.05  
% 0.36/1.05  ------ Superposition Options
% 0.36/1.05  
% 0.36/1.05  --superposition_flag                    true
% 0.36/1.05  --sup_passive_queue_type                priority_queues
% 0.36/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.36/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.36/1.05  --demod_completeness_check              fast
% 0.36/1.05  --demod_use_ground                      true
% 0.36/1.05  --sup_to_prop_solver                    passive
% 0.36/1.05  --sup_prop_simpl_new                    true
% 0.36/1.05  --sup_prop_simpl_given                  true
% 0.36/1.05  --sup_fun_splitting                     true
% 0.36/1.05  --sup_smt_interval                      50000
% 0.36/1.05  
% 0.36/1.05  ------ Superposition Simplification Setup
% 0.36/1.05  
% 0.36/1.05  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 0.36/1.05  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 0.36/1.05  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 0.36/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.36/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 0.36/1.05  --sup_full_bw                           [BwDemod;BwSubsumption]
% 0.36/1.05  --sup_immed_triv                        [TrivRules]
% 0.36/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.05  --sup_immed_bw_main                     []
% 0.36/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 0.36/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.36/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.05  --sup_input_bw                          []
% 0.36/1.05  
% 0.36/1.05  ------ Combination Options
% 0.36/1.05  
% 0.36/1.05  --comb_res_mult                         3
% 0.36/1.05  --comb_sup_mult                         2
% 0.36/1.05  --comb_inst_mult                        10
% 0.36/1.05  
% 0.36/1.05  ------ Debug Options
% 0.36/1.05  
% 0.36/1.05  --dbg_backtrace                         false
% 0.36/1.05  --dbg_dump_prop_clauses                 false
% 0.36/1.05  --dbg_dump_prop_clauses_file            -
% 0.36/1.05  --dbg_out_stat                          false
% 0.36/1.05  
% 0.36/1.05  
% 0.36/1.05  
% 0.36/1.05  
% 0.36/1.05  ------ Proving...
% 0.36/1.05  
% 0.36/1.05  
% 0.36/1.05  % SZS status Theorem for theBenchmark.p
% 0.36/1.05  
% 0.36/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 0.36/1.05  
% 0.36/1.05  fof(f29,conjecture,(
% 0.36/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 0.36/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.05  
% 0.36/1.05  fof(f30,negated_conjecture,(
% 0.36/1.05    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 0.36/1.05    inference(negated_conjecture,[],[f29])).
% 0.36/1.05  
% 0.36/1.05  fof(f64,plain,(
% 0.36/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.36/1.05    inference(ennf_transformation,[],[f30])).
% 0.36/1.05  
% 0.36/1.05  fof(f65,plain,(
% 0.36/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.36/1.05    inference(flattening,[],[f64])).
% 0.36/1.05  
% 0.36/1.05  fof(f79,plain,(
% 0.36/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.36/1.05    inference(nnf_transformation,[],[f65])).
% 0.36/1.05  
% 0.36/1.05  fof(f80,plain,(
% 0.36/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.36/1.05    inference(flattening,[],[f79])).
% 0.36/1.05  
% 0.36/1.05  fof(f84,plain,(
% 0.36/1.05    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK5 = X2 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK5))) )),
% 0.36/1.05    introduced(choice_axiom,[])).
% 0.36/1.05  
% 0.36/1.05  fof(f83,plain,(
% 0.36/1.05    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK4,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK4,X0,X1)) & sK4 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 0.36/1.05    introduced(choice_axiom,[])).
% 0.36/1.05  
% 0.36/1.05  fof(f82,plain,(
% 0.36/1.05    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(X2,X0,sK3)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(X2,X0,sK3)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))) )),
% 0.36/1.05    introduced(choice_axiom,[])).
% 0.36/1.05  
% 0.36/1.05  fof(f81,plain,(
% 0.36/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK2,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK2,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 0.36/1.05    introduced(choice_axiom,[])).
% 0.36/1.05  
% 0.36/1.05  fof(f85,plain,(
% 0.36/1.05    ((((~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK4,sK2,sK3)) & (v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK4,sK2,sK3)) & sK4 = sK5 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 0.36/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f80,f84,f83,f82,f81])).
% 0.36/1.05  
% 0.36/1.05  fof(f147,plain,(
% 0.36/1.05    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))),
% 0.36/1.05    inference(cnf_transformation,[],[f85])).
% 0.36/1.05  
% 0.36/1.05  fof(f22,axiom,(
% 0.36/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.36/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.05  
% 0.36/1.05  fof(f52,plain,(
% 0.36/1.05    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.36/1.05    inference(ennf_transformation,[],[f22])).
% 0.36/1.05  
% 0.36/1.05  fof(f53,plain,(
% 0.36/1.05    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.36/1.05    inference(flattening,[],[f52])).
% 0.36/1.05  
% 0.36/1.05  fof(f126,plain,(
% 0.36/1.05    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.36/1.05    inference(cnf_transformation,[],[f53])).
% 0.36/1.05  
% 0.36/1.05  fof(f145,plain,(
% 0.36/1.05    v1_funct_1(sK5)),
% 0.36/1.05    inference(cnf_transformation,[],[f85])).
% 0.36/1.05  
% 0.36/1.05  fof(f146,plain,(
% 0.36/1.05    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))),
% 0.36/1.05    inference(cnf_transformation,[],[f85])).
% 0.36/1.05  
% 0.36/1.05  fof(f144,plain,(
% 0.36/1.05    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.36/1.05    inference(cnf_transformation,[],[f85])).
% 0.36/1.05  
% 0.36/1.05  fof(f148,plain,(
% 0.36/1.05    sK4 = sK5),
% 0.36/1.05    inference(cnf_transformation,[],[f85])).
% 0.36/1.05  
% 0.36/1.05  fof(f14,axiom,(
% 0.36/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.36/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.05  
% 0.36/1.05  fof(f41,plain,(
% 0.36/1.05    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.36/1.05    inference(ennf_transformation,[],[f14])).
% 0.36/1.05  
% 0.36/1.05  fof(f108,plain,(
% 0.36/1.05    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.36/1.05    inference(cnf_transformation,[],[f41])).
% 0.36/1.05  
% 0.36/1.05  fof(f10,axiom,(
% 0.36/1.05    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.36/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.05  
% 0.36/1.05  fof(f38,plain,(
% 0.36/1.05    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.36/1.05    inference(ennf_transformation,[],[f10])).
% 0.36/1.05  
% 0.36/1.05  fof(f71,plain,(
% 0.36/1.05    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.36/1.05    inference(nnf_transformation,[],[f38])).
% 0.36/1.05  
% 0.36/1.05  fof(f100,plain,(
% 0.36/1.05    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.36/1.05    inference(cnf_transformation,[],[f71])).
% 0.36/1.05  
% 0.36/1.05  fof(f13,axiom,(
% 0.36/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.36/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.05  
% 0.36/1.05  fof(f40,plain,(
% 0.36/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.36/1.05    inference(ennf_transformation,[],[f13])).
% 0.36/1.05  
% 0.36/1.05  fof(f106,plain,(
% 0.36/1.05    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.36/1.05    inference(cnf_transformation,[],[f40])).
% 0.36/1.05  
% 0.36/1.05  fof(f16,axiom,(
% 0.36/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.36/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.05  
% 0.36/1.05  fof(f43,plain,(
% 0.36/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.36/1.05    inference(ennf_transformation,[],[f16])).
% 0.36/1.05  
% 0.36/1.05  fof(f44,plain,(
% 0.36/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.36/1.05    inference(flattening,[],[f43])).
% 0.36/1.05  
% 0.36/1.05  fof(f110,plain,(
% 0.36/1.05    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 0.36/1.05    inference(cnf_transformation,[],[f44])).
% 0.36/1.05  
% 0.36/1.05  fof(f18,axiom,(
% 0.36/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.36/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.05  
% 0.36/1.05  fof(f46,plain,(
% 0.36/1.05    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.36/1.05    inference(ennf_transformation,[],[f18])).
% 0.36/1.05  
% 0.36/1.05  fof(f47,plain,(
% 0.36/1.05    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.36/1.05    inference(flattening,[],[f46])).
% 0.36/1.05  
% 0.36/1.05  fof(f115,plain,(
% 0.36/1.05    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.36/1.05    inference(cnf_transformation,[],[f47])).
% 0.36/1.05  
% 0.36/1.05  fof(f149,plain,(
% 0.36/1.05    v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK4,sK2,sK3)),
% 0.36/1.05    inference(cnf_transformation,[],[f85])).
% 0.36/1.05  
% 0.36/1.05  fof(f28,axiom,(
% 0.36/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 0.36/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.05  
% 0.36/1.05  fof(f62,plain,(
% 0.36/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.36/1.05    inference(ennf_transformation,[],[f28])).
% 0.36/1.05  
% 0.36/1.05  fof(f63,plain,(
% 0.36/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.36/1.05    inference(flattening,[],[f62])).
% 0.36/1.05  
% 0.36/1.05  fof(f78,plain,(
% 0.36/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.36/1.05    inference(nnf_transformation,[],[f63])).
% 0.36/1.05  
% 0.36/1.05  fof(f137,plain,(
% 0.36/1.05    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.36/1.05    inference(cnf_transformation,[],[f78])).
% 0.36/1.05  
% 0.36/1.05  fof(f159,plain,(
% 0.36/1.05    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.36/1.05    inference(equality_resolution,[],[f137])).
% 0.36/1.05  
% 0.36/1.05  fof(f138,plain,(
% 0.36/1.05    v2_pre_topc(sK2)),
% 0.36/1.05    inference(cnf_transformation,[],[f85])).
% 0.36/1.05  
% 0.36/1.05  fof(f139,plain,(
% 0.36/1.05    l1_pre_topc(sK2)),
% 0.36/1.05    inference(cnf_transformation,[],[f85])).
% 0.36/1.05  
% 0.36/1.05  fof(f140,plain,(
% 0.36/1.05    v2_pre_topc(sK3)),
% 0.36/1.05    inference(cnf_transformation,[],[f85])).
% 0.36/1.05  
% 0.36/1.05  fof(f141,plain,(
% 0.36/1.05    l1_pre_topc(sK3)),
% 0.36/1.05    inference(cnf_transformation,[],[f85])).
% 0.36/1.05  
% 0.36/1.05  fof(f26,axiom,(
% 0.36/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.36/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.05  
% 0.36/1.05  fof(f31,plain,(
% 0.36/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.36/1.05    inference(pure_predicate_removal,[],[f26])).
% 0.36/1.05  
% 0.36/1.05  fof(f58,plain,(
% 0.36/1.05    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.36/1.05    inference(ennf_transformation,[],[f31])).
% 0.36/1.05  
% 0.36/1.05  fof(f59,plain,(
% 0.36/1.05    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.36/1.05    inference(flattening,[],[f58])).
% 0.36/1.05  
% 0.36/1.05  fof(f133,plain,(
% 0.36/1.05    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.36/1.05    inference(cnf_transformation,[],[f59])).
% 0.36/1.05  
% 0.36/1.05  fof(f24,axiom,(
% 0.36/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.36/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.05  
% 0.36/1.05  fof(f32,plain,(
% 0.36/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 0.36/1.05    inference(pure_predicate_removal,[],[f24])).
% 0.36/1.05  
% 0.36/1.05  fof(f56,plain,(
% 0.36/1.05    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.36/1.05    inference(ennf_transformation,[],[f32])).
% 0.36/1.05  
% 0.36/1.05  fof(f131,plain,(
% 0.36/1.05    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.36/1.05    inference(cnf_transformation,[],[f56])).
% 0.36/1.05  
% 0.36/1.05  fof(f25,axiom,(
% 0.36/1.05    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.36/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.05  
% 0.36/1.05  fof(f57,plain,(
% 0.36/1.05    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.36/1.05    inference(ennf_transformation,[],[f25])).
% 0.36/1.05  
% 0.36/1.05  fof(f132,plain,(
% 0.36/1.05    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.36/1.05    inference(cnf_transformation,[],[f57])).
% 0.36/1.05  
% 0.36/1.05  fof(f136,plain,(
% 0.36/1.05    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.36/1.05    inference(cnf_transformation,[],[f78])).
% 0.36/1.05  
% 0.36/1.05  fof(f160,plain,(
% 0.36/1.05    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.36/1.05    inference(equality_resolution,[],[f136])).
% 0.36/1.05  
% 0.36/1.05  fof(f150,plain,(
% 0.36/1.05    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK4,sK2,sK3)),
% 0.36/1.05    inference(cnf_transformation,[],[f85])).
% 0.36/1.05  
% 0.36/1.05  fof(f143,plain,(
% 0.36/1.05    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.36/1.05    inference(cnf_transformation,[],[f85])).
% 0.36/1.05  
% 0.36/1.05  fof(f27,axiom,(
% 0.36/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 0.36/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.05  
% 0.36/1.05  fof(f60,plain,(
% 0.36/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.36/1.05    inference(ennf_transformation,[],[f27])).
% 0.36/1.05  
% 0.36/1.05  fof(f61,plain,(
% 0.36/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.36/1.05    inference(flattening,[],[f60])).
% 0.36/1.05  
% 0.36/1.05  fof(f77,plain,(
% 0.36/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.36/1.05    inference(nnf_transformation,[],[f61])).
% 0.36/1.05  
% 0.36/1.05  fof(f135,plain,(
% 0.36/1.05    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.36/1.05    inference(cnf_transformation,[],[f77])).
% 0.36/1.05  
% 0.36/1.05  fof(f157,plain,(
% 0.36/1.05    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.36/1.05    inference(equality_resolution,[],[f135])).
% 0.36/1.05  
% 0.36/1.05  fof(f134,plain,(
% 0.36/1.05    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.36/1.05    inference(cnf_transformation,[],[f77])).
% 0.36/1.05  
% 0.36/1.05  fof(f158,plain,(
% 0.36/1.05    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.36/1.05    inference(equality_resolution,[],[f134])).
% 0.36/1.05  
% 0.36/1.05  cnf(c_55,negated_conjecture,
% 0.36/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
% 0.36/1.05      inference(cnf_transformation,[],[f147]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5641,plain,
% 0.36/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_41,plain,
% 0.36/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 0.36/1.05      | v1_partfun1(X0,X1)
% 0.36/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.05      | ~ v1_funct_1(X0)
% 0.36/1.05      | k1_xboole_0 = X2 ),
% 0.36/1.05      inference(cnf_transformation,[],[f126]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5653,plain,
% 0.36/1.05      ( k1_xboole_0 = X0
% 0.36/1.05      | v1_funct_2(X1,X2,X0) != iProver_top
% 0.36/1.05      | v1_partfun1(X1,X2) = iProver_top
% 0.36/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 0.36/1.05      | v1_funct_1(X1) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_10951,plain,
% 0.36/1.05      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 0.36/1.05      | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top
% 0.36/1.05      | v1_funct_1(sK5) != iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_5641,c_5653]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_57,negated_conjecture,
% 0.36/1.05      ( v1_funct_1(sK5) ),
% 0.36/1.05      inference(cnf_transformation,[],[f145]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_72,plain,
% 0.36/1.05      ( v1_funct_1(sK5) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_56,negated_conjecture,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
% 0.36/1.05      inference(cnf_transformation,[],[f146]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_73,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_58,negated_conjecture,
% 0.36/1.05      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 0.36/1.05      inference(cnf_transformation,[],[f144]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5638,plain,
% 0.36/1.05      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_54,negated_conjecture,
% 0.36/1.05      ( sK4 = sK5 ),
% 0.36/1.05      inference(cnf_transformation,[],[f148]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5681,plain,
% 0.36/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 0.36/1.05      inference(light_normalisation,[status(thm)],[c_5638,c_54]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_21,plain,
% 0.36/1.05      ( v5_relat_1(X0,X1)
% 0.36/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 0.36/1.05      inference(cnf_transformation,[],[f108]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_15,plain,
% 0.36/1.05      ( ~ v5_relat_1(X0,X1)
% 0.36/1.05      | r1_tarski(k2_relat_1(X0),X1)
% 0.36/1.05      | ~ v1_relat_1(X0) ),
% 0.36/1.05      inference(cnf_transformation,[],[f100]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_751,plain,
% 0.36/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.05      | r1_tarski(k2_relat_1(X0),X2)
% 0.36/1.05      | ~ v1_relat_1(X0) ),
% 0.36/1.05      inference(resolution,[status(thm)],[c_21,c_15]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_20,plain,
% 0.36/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.05      | v1_relat_1(X0) ),
% 0.36/1.05      inference(cnf_transformation,[],[f106]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_755,plain,
% 0.36/1.05      ( r1_tarski(k2_relat_1(X0),X2)
% 0.36/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.36/1.05      inference(global_propositional_subsumption,
% 0.36/1.05                [status(thm)],
% 0.36/1.05                [c_751,c_20]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_756,plain,
% 0.36/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.05      | r1_tarski(k2_relat_1(X0),X2) ),
% 0.36/1.05      inference(renaming,[status(thm)],[c_755]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5631,plain,
% 0.36/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 0.36/1.05      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6728,plain,
% 0.36/1.05      ( r1_tarski(k2_relat_1(sK5),u1_struct_0(sK3)) = iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_5681,c_5631]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_24,plain,
% 0.36/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 0.36/1.05      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 0.36/1.05      inference(cnf_transformation,[],[f110]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5664,plain,
% 0.36/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 0.36/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 0.36/1.05      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_9773,plain,
% 0.36/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0))) = iProver_top
% 0.36/1.05      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_5641,c_5664]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_28,plain,
% 0.36/1.05      ( v1_funct_2(X0,X1,X2)
% 0.36/1.05      | ~ v1_partfun1(X0,X1)
% 0.36/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.05      | ~ v1_funct_1(X0) ),
% 0.36/1.05      inference(cnf_transformation,[],[f115]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5663,plain,
% 0.36/1.05      ( v1_funct_2(X0,X1,X2) = iProver_top
% 0.36/1.05      | v1_partfun1(X0,X1) != iProver_top
% 0.36/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 0.36/1.05      | v1_funct_1(X0) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_10385,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0) = iProver_top
% 0.36/1.05      | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 0.36/1.05      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 0.36/1.05      | v1_funct_1(sK5) != iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_9773,c_5663]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_10637,plain,
% 0.36/1.05      ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 0.36/1.05      | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0) = iProver_top ),
% 0.36/1.05      inference(global_propositional_subsumption,
% 0.36/1.05                [status(thm)],
% 0.36/1.05                [c_10385,c_72]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_10638,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0) = iProver_top
% 0.36/1.05      | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 0.36/1.05      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 0.36/1.05      inference(renaming,[status(thm)],[c_10637]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_53,negated_conjecture,
% 0.36/1.05      ( v5_pre_topc(sK4,sK2,sK3)
% 0.36/1.05      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 0.36/1.05      inference(cnf_transformation,[],[f149]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5642,plain,
% 0.36/1.05      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5682,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,sK2,sK3) = iProver_top ),
% 0.36/1.05      inference(light_normalisation,[status(thm)],[c_5642,c_54]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_50,plain,
% 0.36/1.05      ( v5_pre_topc(X0,X1,X2)
% 0.36/1.05      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 0.36/1.05      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 0.36/1.05      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 0.36/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 0.36/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 0.36/1.05      | ~ v2_pre_topc(X1)
% 0.36/1.05      | ~ v2_pre_topc(X2)
% 0.36/1.05      | ~ l1_pre_topc(X1)
% 0.36/1.05      | ~ l1_pre_topc(X2)
% 0.36/1.05      | ~ v1_funct_1(X0) ),
% 0.36/1.05      inference(cnf_transformation,[],[f159]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5645,plain,
% 0.36/1.05      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 0.36/1.05      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 0.36/1.05      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 0.36/1.05      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 0.36/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 0.36/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 0.36/1.05      | v2_pre_topc(X1) != iProver_top
% 0.36/1.05      | v2_pre_topc(X2) != iProver_top
% 0.36/1.05      | l1_pre_topc(X1) != iProver_top
% 0.36/1.05      | l1_pre_topc(X2) != iProver_top
% 0.36/1.05      | v1_funct_1(X0) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_7715,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 0.36/1.05      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 0.36/1.05      | v2_pre_topc(sK3) != iProver_top
% 0.36/1.05      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 0.36/1.05      | l1_pre_topc(sK3) != iProver_top
% 0.36/1.05      | v1_funct_1(sK5) != iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_5641,c_5645]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_64,negated_conjecture,
% 0.36/1.05      ( v2_pre_topc(sK2) ),
% 0.36/1.05      inference(cnf_transformation,[],[f138]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_65,plain,
% 0.36/1.05      ( v2_pre_topc(sK2) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_63,negated_conjecture,
% 0.36/1.05      ( l1_pre_topc(sK2) ),
% 0.36/1.05      inference(cnf_transformation,[],[f139]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_66,plain,
% 0.36/1.05      ( l1_pre_topc(sK2) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_62,negated_conjecture,
% 0.36/1.05      ( v2_pre_topc(sK3) ),
% 0.36/1.05      inference(cnf_transformation,[],[f140]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_67,plain,
% 0.36/1.05      ( v2_pre_topc(sK3) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_61,negated_conjecture,
% 0.36/1.05      ( l1_pre_topc(sK3) ),
% 0.36/1.05      inference(cnf_transformation,[],[f141]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_68,plain,
% 0.36/1.05      ( l1_pre_topc(sK3) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_47,plain,
% 0.36/1.05      ( ~ v2_pre_topc(X0)
% 0.36/1.05      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 0.36/1.05      | ~ l1_pre_topc(X0) ),
% 0.36/1.05      inference(cnf_transformation,[],[f133]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5826,plain,
% 0.36/1.05      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 0.36/1.05      | ~ v2_pre_topc(sK2)
% 0.36/1.05      | ~ l1_pre_topc(sK2) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_47]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5827,plain,
% 0.36/1.05      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 0.36/1.05      | v2_pre_topc(sK2) != iProver_top
% 0.36/1.05      | l1_pre_topc(sK2) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_5826]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_45,plain,
% 0.36/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 0.36/1.05      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 0.36/1.05      inference(cnf_transformation,[],[f131]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6084,plain,
% 0.36/1.05      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.36/1.05      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_45]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6085,plain,
% 0.36/1.05      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 0.36/1.05      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_6084]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_46,plain,
% 0.36/1.05      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 0.36/1.05      | ~ l1_pre_topc(X0) ),
% 0.36/1.05      inference(cnf_transformation,[],[f132]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6336,plain,
% 0.36/1.05      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 0.36/1.05      | ~ l1_pre_topc(sK2) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_46]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6337,plain,
% 0.36/1.05      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 0.36/1.05      | l1_pre_topc(sK2) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_6336]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_51,plain,
% 0.36/1.05      ( ~ v5_pre_topc(X0,X1,X2)
% 0.36/1.05      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 0.36/1.05      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 0.36/1.05      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 0.36/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 0.36/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 0.36/1.05      | ~ v2_pre_topc(X1)
% 0.36/1.05      | ~ v2_pre_topc(X2)
% 0.36/1.05      | ~ l1_pre_topc(X1)
% 0.36/1.05      | ~ l1_pre_topc(X2)
% 0.36/1.05      | ~ v1_funct_1(X0) ),
% 0.36/1.05      inference(cnf_transformation,[],[f160]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5644,plain,
% 0.36/1.05      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 0.36/1.05      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 0.36/1.05      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 0.36/1.05      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 0.36/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 0.36/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 0.36/1.05      | v2_pre_topc(X1) != iProver_top
% 0.36/1.05      | v2_pre_topc(X2) != iProver_top
% 0.36/1.05      | l1_pre_topc(X1) != iProver_top
% 0.36/1.05      | l1_pre_topc(X2) != iProver_top
% 0.36/1.05      | v1_funct_1(X0) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_7323,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 0.36/1.05      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 0.36/1.05      | v2_pre_topc(sK3) != iProver_top
% 0.36/1.05      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 0.36/1.05      | l1_pre_topc(sK3) != iProver_top
% 0.36/1.05      | v1_funct_1(sK5) != iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_5641,c_5644]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_52,negated_conjecture,
% 0.36/1.05      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 0.36/1.05      | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 0.36/1.05      inference(cnf_transformation,[],[f150]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5643,plain,
% 0.36/1.05      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5683,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,sK2,sK3) != iProver_top ),
% 0.36/1.05      inference(light_normalisation,[status(thm)],[c_5643,c_54]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_59,negated_conjecture,
% 0.36/1.05      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 0.36/1.05      inference(cnf_transformation,[],[f143]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5637,plain,
% 0.36/1.05      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5680,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 0.36/1.05      inference(light_normalisation,[status(thm)],[c_5637,c_54]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_48,plain,
% 0.36/1.05      ( v5_pre_topc(X0,X1,X2)
% 0.36/1.05      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 0.36/1.05      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 0.36/1.05      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 0.36/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 0.36/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 0.36/1.05      | ~ v2_pre_topc(X1)
% 0.36/1.05      | ~ v2_pre_topc(X2)
% 0.36/1.05      | ~ l1_pre_topc(X1)
% 0.36/1.05      | ~ l1_pre_topc(X2)
% 0.36/1.05      | ~ v1_funct_1(X0) ),
% 0.36/1.05      inference(cnf_transformation,[],[f157]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6004,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,X0,sK3)
% 0.36/1.05      | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3)
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))))
% 0.36/1.05      | ~ v2_pre_topc(X0)
% 0.36/1.05      | ~ v2_pre_topc(sK3)
% 0.36/1.05      | ~ l1_pre_topc(X0)
% 0.36/1.05      | ~ l1_pre_topc(sK3)
% 0.36/1.05      | ~ v1_funct_1(sK5) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_48]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6652,plain,
% 0.36/1.05      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 0.36/1.05      | v5_pre_topc(sK5,sK2,sK3)
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 0.36/1.05      | ~ v2_pre_topc(sK3)
% 0.36/1.05      | ~ v2_pre_topc(sK2)
% 0.36/1.05      | ~ l1_pre_topc(sK3)
% 0.36/1.05      | ~ l1_pre_topc(sK2)
% 0.36/1.05      | ~ v1_funct_1(sK5) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_6004]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6653,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,sK2,sK3) = iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 0.36/1.05      | v2_pre_topc(sK3) != iProver_top
% 0.36/1.05      | v2_pre_topc(sK2) != iProver_top
% 0.36/1.05      | l1_pre_topc(sK3) != iProver_top
% 0.36/1.05      | l1_pre_topc(sK2) != iProver_top
% 0.36/1.05      | v1_funct_1(sK5) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_6652]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_7433,plain,
% 0.36/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top ),
% 0.36/1.05      inference(global_propositional_subsumption,
% 0.36/1.05                [status(thm)],
% 0.36/1.05                [c_7323,c_65,c_66,c_67,c_68,c_72,c_73,c_5683,c_5680,
% 0.36/1.05                 c_5681,c_5827,c_6085,c_6337,c_6653]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_7434,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 0.36/1.05      inference(renaming,[status(thm)],[c_7433]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_8016,plain,
% 0.36/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 0.36/1.05      inference(global_propositional_subsumption,
% 0.36/1.05                [status(thm)],
% 0.36/1.05                [c_7715,c_65,c_66,c_67,c_68,c_72,c_73,c_5683,c_5680,
% 0.36/1.05                 c_5681,c_5827,c_6085,c_6337,c_6653,c_7323]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_8017,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 0.36/1.05      inference(renaming,[status(thm)],[c_8016]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_8020,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,sK2,sK3) = iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_5682,c_8017]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_49,plain,
% 0.36/1.05      ( ~ v5_pre_topc(X0,X1,X2)
% 0.36/1.05      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 0.36/1.05      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 0.36/1.05      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 0.36/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 0.36/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 0.36/1.05      | ~ v2_pre_topc(X1)
% 0.36/1.05      | ~ v2_pre_topc(X2)
% 0.36/1.05      | ~ l1_pre_topc(X1)
% 0.36/1.05      | ~ l1_pre_topc(X2)
% 0.36/1.05      | ~ v1_funct_1(X0) ),
% 0.36/1.05      inference(cnf_transformation,[],[f158]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6554,plain,
% 0.36/1.05      ( ~ v5_pre_topc(sK5,X0,sK3)
% 0.36/1.05      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3)
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))))
% 0.36/1.05      | ~ v2_pre_topc(X0)
% 0.36/1.05      | ~ v2_pre_topc(sK3)
% 0.36/1.05      | ~ l1_pre_topc(X0)
% 0.36/1.05      | ~ l1_pre_topc(sK3)
% 0.36/1.05      | ~ v1_funct_1(sK5) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_49]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_8126,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 0.36/1.05      | ~ v5_pre_topc(sK5,sK2,sK3)
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 0.36/1.05      | ~ v2_pre_topc(sK3)
% 0.36/1.05      | ~ v2_pre_topc(sK2)
% 0.36/1.05      | ~ l1_pre_topc(sK3)
% 0.36/1.05      | ~ l1_pre_topc(sK2)
% 0.36/1.05      | ~ v1_funct_1(sK5) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_6554]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_8127,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,sK2,sK3) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 0.36/1.05      | v2_pre_topc(sK3) != iProver_top
% 0.36/1.05      | v2_pre_topc(sK2) != iProver_top
% 0.36/1.05      | l1_pre_topc(sK3) != iProver_top
% 0.36/1.05      | l1_pre_topc(sK2) != iProver_top
% 0.36/1.05      | v1_funct_1(sK5) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_8126]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_8147,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 0.36/1.05      inference(global_propositional_subsumption,
% 0.36/1.05                [status(thm)],
% 0.36/1.05                [c_8020,c_65,c_66,c_67,c_68,c_72,c_5680,c_5681,c_7434,
% 0.36/1.05                 c_8127]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_10010,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | r1_tarski(k2_relat_1(sK5),u1_struct_0(sK3)) != iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_9773,c_8147]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_10167,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 0.36/1.05      inference(global_propositional_subsumption,
% 0.36/1.05                [status(thm)],
% 0.36/1.05                [c_10010,c_6728]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_10643,plain,
% 0.36/1.05      ( v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 0.36/1.05      | r1_tarski(k2_relat_1(sK5),u1_struct_0(sK3)) != iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_10638,c_10167]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_11878,plain,
% 0.36/1.05      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0 ),
% 0.36/1.05      inference(global_propositional_subsumption,
% 0.36/1.05                [status(thm)],
% 0.36/1.05                [c_10951,c_72,c_73,c_6728,c_10643]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_10953,plain,
% 0.36/1.05      ( u1_struct_0(sK3) = k1_xboole_0
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | v1_partfun1(sK5,u1_struct_0(sK2)) = iProver_top
% 0.36/1.05      | v1_funct_1(sK5) != iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_5681,c_5653]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6726,plain,
% 0.36/1.05      ( r1_tarski(k2_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_5641,c_5631]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_9775,plain,
% 0.36/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0))) = iProver_top
% 0.36/1.05      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_5681,c_5664]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_10386,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(sK2),X0) = iProver_top
% 0.36/1.05      | v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
% 0.36/1.05      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 0.36/1.05      | v1_funct_1(sK5) != iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_9775,c_5663]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_10628,plain,
% 0.36/1.05      ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 0.36/1.05      | v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(sK2),X0) = iProver_top ),
% 0.36/1.05      inference(global_propositional_subsumption,
% 0.36/1.05                [status(thm)],
% 0.36/1.05                [c_10386,c_72]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_10629,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(sK2),X0) = iProver_top
% 0.36/1.05      | v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
% 0.36/1.05      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 0.36/1.05      inference(renaming,[status(thm)],[c_10628]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5646,plain,
% 0.36/1.05      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 0.36/1.05      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 0.36/1.05      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 0.36/1.05      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 0.36/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 0.36/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 0.36/1.05      | v2_pre_topc(X1) != iProver_top
% 0.36/1.05      | v2_pre_topc(X2) != iProver_top
% 0.36/1.05      | l1_pre_topc(X1) != iProver_top
% 0.36/1.05      | l1_pre_topc(X2) != iProver_top
% 0.36/1.05      | v1_funct_1(X0) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_8170,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 0.36/1.05      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 0.36/1.05      | v2_pre_topc(sK2) != iProver_top
% 0.36/1.05      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 0.36/1.05      | l1_pre_topc(sK2) != iProver_top
% 0.36/1.05      | v1_funct_1(sK5) != iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_5641,c_5646]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_74,plain,
% 0.36/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5841,plain,
% 0.36/1.05      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 0.36/1.05      | ~ v2_pre_topc(sK3)
% 0.36/1.05      | ~ l1_pre_topc(sK3) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_47]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5842,plain,
% 0.36/1.05      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 0.36/1.05      | v2_pre_topc(sK3) != iProver_top
% 0.36/1.05      | l1_pre_topc(sK3) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_5841]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6094,plain,
% 0.36/1.05      ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 0.36/1.05      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_45]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6095,plain,
% 0.36/1.05      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 0.36/1.05      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_6094]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6347,plain,
% 0.36/1.05      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 0.36/1.05      | ~ l1_pre_topc(sK3) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_46]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6348,plain,
% 0.36/1.05      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
% 0.36/1.05      | l1_pre_topc(sK3) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_6347]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6005,plain,
% 0.36/1.05      ( ~ v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 0.36/1.05      | v5_pre_topc(sK5,X0,sK3)
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 0.36/1.05      | ~ v2_pre_topc(X0)
% 0.36/1.05      | ~ v2_pre_topc(sK3)
% 0.36/1.05      | ~ l1_pre_topc(X0)
% 0.36/1.05      | ~ l1_pre_topc(sK3)
% 0.36/1.05      | ~ v1_funct_1(sK5) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_50]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6625,plain,
% 0.36/1.05      ( ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 0.36/1.05      | v5_pre_topc(sK5,sK2,sK3)
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 0.36/1.05      | ~ v2_pre_topc(sK3)
% 0.36/1.05      | ~ v2_pre_topc(sK2)
% 0.36/1.05      | ~ l1_pre_topc(sK3)
% 0.36/1.05      | ~ l1_pre_topc(sK2)
% 0.36/1.05      | ~ v1_funct_1(sK5) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_6005]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6626,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,sK2,sK3) = iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 0.36/1.05      | v2_pre_topc(sK3) != iProver_top
% 0.36/1.05      | v2_pre_topc(sK2) != iProver_top
% 0.36/1.05      | l1_pre_topc(sK3) != iProver_top
% 0.36/1.05      | l1_pre_topc(sK2) != iProver_top
% 0.36/1.05      | v1_funct_1(sK5) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_6625]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_7029,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 0.36/1.05      | ~ v5_pre_topc(sK5,sK2,sK3)
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 0.36/1.05      | ~ v2_pre_topc(sK3)
% 0.36/1.05      | ~ v2_pre_topc(sK2)
% 0.36/1.05      | ~ l1_pre_topc(sK3)
% 0.36/1.05      | ~ l1_pre_topc(sK2)
% 0.36/1.05      | ~ v1_funct_1(sK5) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_51]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_7030,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,sK2,sK3) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 0.36/1.05      | v2_pre_topc(sK3) != iProver_top
% 0.36/1.05      | v2_pre_topc(sK2) != iProver_top
% 0.36/1.05      | l1_pre_topc(sK3) != iProver_top
% 0.36/1.05      | l1_pre_topc(sK2) != iProver_top
% 0.36/1.05      | v1_funct_1(sK5) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_7029]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_6292,plain,
% 0.36/1.05      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)
% 0.36/1.05      | v5_pre_topc(sK5,sK2,X0)
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X0))
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(X0))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X0))))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 0.36/1.05      | ~ v2_pre_topc(X0)
% 0.36/1.05      | ~ v2_pre_topc(sK2)
% 0.36/1.05      | ~ l1_pre_topc(X0)
% 0.36/1.05      | ~ l1_pre_topc(sK2)
% 0.36/1.05      | ~ v1_funct_1(sK5) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_48]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_7166,plain,
% 0.36/1.05      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 0.36/1.05      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 0.36/1.05      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 0.36/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 0.36/1.05      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 0.36/1.05      | ~ v2_pre_topc(sK2)
% 0.36/1.05      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 0.36/1.05      | ~ l1_pre_topc(sK2)
% 0.36/1.05      | ~ v1_funct_1(sK5) ),
% 0.36/1.05      inference(instantiation,[status(thm)],[c_6292]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_7167,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 0.36/1.05      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 0.36/1.05      | v2_pre_topc(sK2) != iProver_top
% 0.36/1.05      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 0.36/1.05      | l1_pre_topc(sK2) != iProver_top
% 0.36/1.05      | v1_funct_1(sK5) != iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_7166]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_8654,plain,
% 0.36/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 0.36/1.05      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 0.36/1.05      inference(global_propositional_subsumption,
% 0.36/1.05                [status(thm)],
% 0.36/1.05                [c_8170,c_65,c_66,c_67,c_68,c_72,c_73,c_74,c_5683,c_5680,
% 0.36/1.05                 c_5681,c_5682,c_5842,c_6095,c_6348,c_6626,c_7030,c_7167]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_8655,plain,
% 0.36/1.05      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 0.36/1.05      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 0.36/1.05      inference(renaming,[status(thm)],[c_8654]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_8658,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 0.36/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 0.36/1.05      inference(global_propositional_subsumption,
% 0.36/1.05                [status(thm)],
% 0.36/1.05                [c_8655,c_65,c_66,c_67,c_68,c_72,c_73,c_74,c_5680,c_5681,
% 0.36/1.05                 c_5682,c_5842,c_6095,c_6348,c_7030,c_7167]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_9878,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 0.36/1.05      | r1_tarski(k2_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_9775,c_8658]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_10242,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 0.36/1.05      inference(global_propositional_subsumption,
% 0.36/1.05                [status(thm)],
% 0.36/1.05                [c_9878,c_6726]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_10634,plain,
% 0.36/1.05      ( v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
% 0.36/1.05      | r1_tarski(k2_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 0.36/1.05      inference(superposition,[status(thm)],[c_10629,c_10242]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_11330,plain,
% 0.36/1.05      ( u1_struct_0(sK3) = k1_xboole_0 ),
% 0.36/1.05      inference(global_propositional_subsumption,
% 0.36/1.05                [status(thm)],
% 0.36/1.05                [c_10953,c_72,c_5680,c_6726,c_10634]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_11880,plain,
% 0.36/1.05      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3))) = k1_xboole_0 ),
% 0.36/1.05      inference(light_normalisation,[status(thm)],[c_11878,c_11330]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_5640,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 0.36/1.05      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_11347,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))) = iProver_top ),
% 0.36/1.05      inference(demodulation,[status(thm)],[c_11330,c_5640]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_11882,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = iProver_top ),
% 0.36/1.05      inference(demodulation,[status(thm)],[c_11880,c_11347]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(c_11333,plain,
% 0.36/1.05      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) != iProver_top ),
% 0.36/1.05      inference(demodulation,[status(thm)],[c_11330,c_10167]) ).
% 0.36/1.05  
% 0.36/1.05  cnf(contradiction,plain,
% 0.36/1.05      ( $false ),
% 0.36/1.05      inference(minisat,[status(thm)],[c_11882,c_11333]) ).
% 0.36/1.05  
% 0.36/1.05  
% 0.36/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 0.36/1.05  
% 0.36/1.05  ------                               Statistics
% 0.36/1.05  
% 0.36/1.05  ------ General
% 0.36/1.05  
% 0.36/1.05  abstr_ref_over_cycles:                  0
% 0.36/1.05  abstr_ref_under_cycles:                 0
% 0.36/1.05  gc_basic_clause_elim:                   0
% 0.36/1.05  forced_gc_time:                         0
% 0.36/1.05  parsing_time:                           0.012
% 0.36/1.05  unif_index_cands_time:                  0.
% 0.36/1.05  unif_index_add_time:                    0.
% 0.36/1.05  orderings_time:                         0.
% 0.36/1.05  out_proof_time:                         0.026
% 0.36/1.05  total_time:                             0.434
% 0.36/1.05  num_of_symbols:                         59
% 0.36/1.05  num_of_terms:                           8821
% 0.36/1.05  
% 0.36/1.05  ------ Preprocessing
% 0.36/1.05  
% 0.36/1.05  num_of_splits:                          0
% 0.36/1.05  num_of_split_atoms:                     0
% 0.36/1.05  num_of_reused_defs:                     0
% 0.36/1.05  num_eq_ax_congr_red:                    29
% 0.36/1.05  num_of_sem_filtered_clauses:            1
% 0.36/1.05  num_of_subtypes:                        0
% 0.36/1.05  monotx_restored_types:                  0
% 0.36/1.05  sat_num_of_epr_types:                   0
% 0.36/1.05  sat_num_of_non_cyclic_types:            0
% 0.36/1.05  sat_guarded_non_collapsed_types:        0
% 0.36/1.05  num_pure_diseq_elim:                    0
% 0.36/1.05  simp_replaced_by:                       0
% 0.36/1.05  res_preprocessed:                       276
% 0.36/1.05  prep_upred:                             0
% 0.36/1.05  prep_unflattend:                        134
% 0.36/1.05  smt_new_axioms:                         0
% 0.36/1.05  pred_elim_cands:                        11
% 0.36/1.05  pred_elim:                              2
% 0.36/1.05  pred_elim_cl:                           3
% 0.36/1.05  pred_elim_cycles:                       10
% 0.36/1.05  merged_defs:                            16
% 0.36/1.05  merged_defs_ncl:                        0
% 0.36/1.05  bin_hyper_res:                          18
% 0.36/1.05  prep_cycles:                            4
% 0.36/1.05  pred_elim_time:                         0.07
% 0.36/1.05  splitting_time:                         0.
% 0.36/1.05  sem_filter_time:                        0.
% 0.36/1.05  monotx_time:                            0.001
% 0.36/1.05  subtype_inf_time:                       0.
% 0.36/1.05  
% 0.36/1.05  ------ Problem properties
% 0.36/1.05  
% 0.36/1.05  clauses:                                58
% 0.36/1.05  conjectures:                            13
% 0.36/1.05  epr:                                    15
% 0.36/1.05  horn:                                   53
% 0.36/1.05  ground:                                 16
% 0.36/1.05  unary:                                  26
% 0.36/1.05  binary:                                 13
% 0.36/1.05  lits:                                   150
% 0.36/1.05  lits_eq:                                16
% 0.36/1.05  fd_pure:                                0
% 0.36/1.05  fd_pseudo:                              0
% 0.36/1.05  fd_cond:                                7
% 0.36/1.05  fd_pseudo_cond:                         2
% 0.36/1.05  ac_symbols:                             0
% 0.36/1.05  
% 0.36/1.05  ------ Propositional Solver
% 0.36/1.05  
% 0.36/1.05  prop_solver_calls:                      30
% 0.36/1.05  prop_fast_solver_calls:                 2651
% 0.36/1.05  smt_solver_calls:                       0
% 0.36/1.05  smt_fast_solver_calls:                  0
% 0.36/1.05  prop_num_of_clauses:                    3848
% 0.36/1.05  prop_preprocess_simplified:             11867
% 0.36/1.05  prop_fo_subsumed:                       109
% 0.36/1.05  prop_solver_time:                       0.
% 0.36/1.05  smt_solver_time:                        0.
% 0.36/1.05  smt_fast_solver_time:                   0.
% 0.36/1.05  prop_fast_solver_time:                  0.
% 0.36/1.05  prop_unsat_core_time:                   0.
% 0.36/1.05  
% 0.36/1.05  ------ QBF
% 0.36/1.05  
% 0.36/1.05  qbf_q_res:                              0
% 0.36/1.05  qbf_num_tautologies:                    0
% 0.36/1.05  qbf_prep_cycles:                        0
% 0.36/1.05  
% 0.36/1.05  ------ BMC1
% 0.36/1.05  
% 0.36/1.05  bmc1_current_bound:                     -1
% 0.36/1.05  bmc1_last_solved_bound:                 -1
% 0.36/1.05  bmc1_unsat_core_size:                   -1
% 0.36/1.05  bmc1_unsat_core_parents_size:           -1
% 0.36/1.05  bmc1_merge_next_fun:                    0
% 0.36/1.05  bmc1_unsat_core_clauses_time:           0.
% 0.36/1.05  
% 0.36/1.05  ------ Instantiation
% 0.36/1.05  
% 0.36/1.05  inst_num_of_clauses:                    995
% 0.36/1.05  inst_num_in_passive:                    15
% 0.36/1.05  inst_num_in_active:                     486
% 0.36/1.05  inst_num_in_unprocessed:                494
% 0.36/1.05  inst_num_of_loops:                      590
% 0.36/1.05  inst_num_of_learning_restarts:          0
% 0.36/1.05  inst_num_moves_active_passive:          100
% 0.36/1.05  inst_lit_activity:                      0
% 0.36/1.05  inst_lit_activity_moves:                0
% 0.36/1.05  inst_num_tautologies:                   0
% 0.36/1.05  inst_num_prop_implied:                  0
% 0.36/1.05  inst_num_existing_simplified:           0
% 0.36/1.05  inst_num_eq_res_simplified:             0
% 0.36/1.05  inst_num_child_elim:                    0
% 0.36/1.05  inst_num_of_dismatching_blockings:      294
% 0.36/1.05  inst_num_of_non_proper_insts:           1056
% 0.36/1.05  inst_num_of_duplicates:                 0
% 0.36/1.05  inst_inst_num_from_inst_to_res:         0
% 0.36/1.05  inst_dismatching_checking_time:         0.
% 0.36/1.05  
% 0.36/1.05  ------ Resolution
% 0.36/1.05  
% 0.36/1.05  res_num_of_clauses:                     0
% 0.36/1.05  res_num_in_passive:                     0
% 0.36/1.05  res_num_in_active:                      0
% 0.36/1.05  res_num_of_loops:                       280
% 0.36/1.05  res_forward_subset_subsumed:            106
% 0.36/1.05  res_backward_subset_subsumed:           4
% 0.36/1.05  res_forward_subsumed:                   4
% 0.36/1.05  res_backward_subsumed:                  0
% 0.36/1.05  res_forward_subsumption_resolution:     17
% 0.36/1.05  res_backward_subsumption_resolution:    0
% 0.36/1.05  res_clause_to_clause_subsumption:       808
% 0.36/1.05  res_orphan_elimination:                 0
% 0.36/1.05  res_tautology_del:                      96
% 0.36/1.05  res_num_eq_res_simplified:              0
% 0.36/1.05  res_num_sel_changes:                    0
% 0.36/1.05  res_moves_from_active_to_pass:          0
% 0.36/1.05  
% 0.36/1.05  ------ Superposition
% 0.36/1.05  
% 0.36/1.05  sup_time_total:                         0.
% 0.36/1.05  sup_time_generating:                    0.
% 0.36/1.05  sup_time_sim_full:                      0.
% 0.36/1.05  sup_time_sim_immed:                     0.
% 0.36/1.05  
% 0.36/1.05  sup_num_of_clauses:                     226
% 0.36/1.05  sup_num_in_active:                      89
% 0.36/1.05  sup_num_in_passive:                     137
% 0.36/1.05  sup_num_of_loops:                       117
% 0.36/1.05  sup_fw_superposition:                   180
% 0.36/1.05  sup_bw_superposition:                   87
% 0.36/1.05  sup_immediate_simplified:               55
% 0.36/1.05  sup_given_eliminated:                   0
% 0.36/1.05  comparisons_done:                       0
% 0.36/1.05  comparisons_avoided:                    0
% 0.36/1.05  
% 0.36/1.05  ------ Simplifications
% 0.36/1.05  
% 0.36/1.05  
% 0.36/1.05  sim_fw_subset_subsumed:                 25
% 0.36/1.05  sim_bw_subset_subsumed:                 8
% 0.36/1.05  sim_fw_subsumed:                        14
% 0.36/1.05  sim_bw_subsumed:                        3
% 0.36/1.05  sim_fw_subsumption_res:                 0
% 0.36/1.05  sim_bw_subsumption_res:                 0
% 0.36/1.05  sim_tautology_del:                      10
% 0.36/1.05  sim_eq_tautology_del:                   6
% 0.36/1.05  sim_eq_res_simp:                        0
% 0.36/1.05  sim_fw_demodulated:                     14
% 0.36/1.05  sim_bw_demodulated:                     21
% 0.36/1.05  sim_light_normalised:                   18
% 0.36/1.05  sim_joinable_taut:                      0
% 0.36/1.05  sim_joinable_simp:                      0
% 0.36/1.05  sim_ac_normalised:                      0
% 0.36/1.05  sim_smt_subsumption:                    0
% 0.36/1.05  
%------------------------------------------------------------------------------
