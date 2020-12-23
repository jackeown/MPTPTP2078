%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:50 EST 2020

% Result     : Theorem 24.08s
% Output     : CNFRefutation 24.08s
% Verified   : 
% Statistics : Number of formulae       :  418 (275266 expanded)
%              Number of clauses        :  302 (67993 expanded)
%              Number of leaves         :   34 (83843 expanded)
%              Depth                    :   42
%              Number of atoms          : 1637 (3030750 expanded)
%              Number of equality atoms :  688 (309456 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f102,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
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

fof(f39,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f101,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f66,plain,(
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
    inference(flattening,[],[f65])).

fof(f70,plain,(
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

fof(f69,plain,(
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

fof(f68,plain,(
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

fof(f67,plain,
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

fof(f71,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f66,f70,f69,f68,f67])).

fof(f114,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f71])).

fof(f118,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f71])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f115,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f113,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f71])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f117,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    inference(cnf_transformation,[],[f71])).

fof(f116,plain,(
    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(cnf_transformation,[],[f71])).

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

fof(f41,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f103,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f111,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f119,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f71])).

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

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f105,plain,(
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
    inference(cnf_transformation,[],[f63])).

fof(f124,plain,(
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
    inference(equality_resolution,[],[f105])).

fof(f108,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f109,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f110,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f120,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f71])).

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

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f107,plain,(
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
    inference(cnf_transformation,[],[f64])).

fof(f126,plain,(
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
    inference(equality_resolution,[],[f107])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f54,f55])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f104,plain,(
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
    inference(cnf_transformation,[],[f63])).

fof(f125,plain,(
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
    inference(equality_resolution,[],[f104])).

fof(f106,plain,(
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
    inference(cnf_transformation,[],[f64])).

fof(f127,plain,(
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
    inference(equality_resolution,[],[f106])).

fof(f15,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f61,plain,(
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

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK2(X0,X1),X0,X1)
      & v1_funct_1(sK2(X0,X1))
      & v4_relat_1(sK2(X0,X1),X0)
      & v1_relat_1(sK2(X0,X1))
      & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f61])).

fof(f96,plain,(
    ! [X0,X1] : m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f62])).

fof(f97,plain,(
    ! [X0,X1] : v1_relat_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

fof(f99,plain,(
    ! [X0,X1] : v1_funct_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

fof(f100,plain,(
    ! [X0,X1] : v1_funct_2(sK2(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f62])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f86,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f57])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f121,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f81])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f122,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f80])).

cnf(c_30,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3835,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3836,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7398,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3835,c_3836])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3824,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_38,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_3887,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3824,c_38])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3844,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6674,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3887,c_3844])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_340,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_341,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_340])).

cnf(c_427,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_341])).

cnf(c_3816,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_13723,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_6674,c_3816])).

cnf(c_2847,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2846,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6901,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_2847,c_2846])).

cnf(c_7143,plain,
    ( sK6 = sK5 ),
    inference(resolution,[status(thm)],[c_6901,c_38])).

cnf(c_2853,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7154,plain,
    ( ~ v1_relat_1(sK5)
    | v1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_7143,c_2853])).

cnf(c_7160,plain,
    ( v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7154])).

cnf(c_4675,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_11,c_42])).

cnf(c_10265,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))
    | v1_relat_1(sK5) ),
    inference(resolution,[status(thm)],[c_427,c_4675])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_10697,plain,
    ( v1_relat_1(sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10265,c_13])).

cnf(c_10698,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10697])).

cnf(c_14330,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13723,c_7160,c_10698])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_23,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_654,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_17,c_23])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_658,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_654,c_15])).

cnf(c_3815,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_4305,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3887,c_3815])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_56,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3823,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_3878,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3823,c_38])).

cnf(c_4708,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4305,c_56,c_3878])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3841,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8212,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3887,c_3841])).

cnf(c_8379,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4708,c_8212])).

cnf(c_14338,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_14330,c_8379])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3846,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_14378,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14338,c_3846])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_3827,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_46616,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14378,c_3827])).

cnf(c_48796,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | sK6 = k1_xboole_0
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_46616,c_3815])).

cnf(c_7151,plain,
    ( X0 != sK5
    | sK6 = X0 ),
    inference(resolution,[status(thm)],[c_7143,c_2847])).

cnf(c_7804,plain,
    ( ~ v1_xboole_0(sK5)
    | sK6 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7151,c_6])).

cnf(c_2852,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_7447,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_2852,c_2846])).

cnf(c_17054,plain,
    ( m1_subset_1(sK5,X0)
    | ~ m1_subset_1(sK6,X0) ),
    inference(resolution,[status(thm)],[c_7447,c_38])).

cnf(c_17169,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | r1_tarski(sK5,X0) ),
    inference(resolution,[status(thm)],[c_17054,c_11])).

cnf(c_17937,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) ),
    inference(resolution,[status(thm)],[c_17169,c_39])).

cnf(c_6810,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_16,c_10])).

cnf(c_18631,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_17937,c_6810])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3826,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_46617,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14378,c_3826])).

cnf(c_47652,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_46617])).

cnf(c_48865,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_48796])).

cnf(c_51595,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_48796,c_41,c_7154,c_7804,c_10697,c_18631,c_47652,c_48865])).

cnf(c_31,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3834,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_51621,plain,
    ( sK6 = k1_xboole_0
    | v2_pre_topc(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))))) = iProver_top
    | v2_pre_topc(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_51595,c_3834])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_52,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_37,negated_conjecture,
    ( v5_pre_topc(sK5,sK3,sK4)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3828,plain,
    ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3962,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3828,c_38])).

cnf(c_32,plain,
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
    inference(cnf_transformation,[],[f124])).

cnf(c_3833,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_8019,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3827,c_3833])).

cnf(c_48,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_49,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_50,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_51,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_57,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_36,negated_conjecture,
    ( ~ v5_pre_topc(sK5,sK3,sK4)
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_3829,plain,
    ( v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3967,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,sK3,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3829,c_38])).

cnf(c_34,plain,
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
    inference(cnf_transformation,[],[f126])).

cnf(c_4346,plain,
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
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_4347,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4346])).

cnf(c_8583,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8019,c_49,c_50,c_51,c_52,c_56,c_57,c_3878,c_3967,c_3887,c_4347])).

cnf(c_8584,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8583])).

cnf(c_8592,plain,
    ( v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3962,c_8584])).

cnf(c_46599,plain,
    ( sK6 = k1_xboole_0
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14378,c_8592])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_133,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3849,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3851,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7284,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3849,c_3851])).

cnf(c_3845,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8723,plain,
    ( v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3845,c_8592])).

cnf(c_8839,plain,
    ( v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7284,c_8723])).

cnf(c_13023,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_13024,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13023])).

cnf(c_2848,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7904,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2848])).

cnf(c_15584,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7904])).

cnf(c_15585,plain,
    ( sK6 != k1_xboole_0
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15584])).

cnf(c_46596,plain,
    ( sK6 = k1_xboole_0
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14378,c_8723])).

cnf(c_6673,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3827,c_3844])).

cnf(c_46608,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14378,c_6673])).

cnf(c_51672,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_51595,c_46608])).

cnf(c_52546,plain,
    ( v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46599,c_51,c_52,c_133,c_8839,c_13024,c_15585,c_46596,c_51672])).

cnf(c_52553,plain,
    ( sK6 = k1_xboole_0
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14378,c_52546])).

cnf(c_51675,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_51595,c_46617])).

cnf(c_51674,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_51595,c_46616])).

cnf(c_33,plain,
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
    inference(cnf_transformation,[],[f125])).

cnf(c_3832,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7211,plain,
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
    inference(superposition,[status(thm)],[c_3827,c_3832])).

cnf(c_7410,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7211,c_49,c_50,c_51,c_52,c_56,c_57,c_3878,c_3967,c_3887,c_4347])).

cnf(c_7411,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7410])).

cnf(c_46602,plain,
    ( sK6 = k1_xboole_0
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14378,c_7411])).

cnf(c_7419,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3845,c_7411])).

cnf(c_7857,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7284,c_7419])).

cnf(c_50353,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46602,c_51,c_52,c_133,c_7857,c_13024,c_15585])).

cnf(c_50354,plain,
    ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_50353])).

cnf(c_52530,plain,
    ( sK6 = k1_xboole_0
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_51674,c_50354])).

cnf(c_46600,plain,
    ( sK6 = k1_xboole_0
    | v5_pre_topc(sK6,g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14378,c_8584])).

cnf(c_8465,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6) ),
    inference(resolution,[status(thm)],[c_32,c_39])).

cnf(c_8585,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8584])).

cnf(c_8755,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8465,c_8585])).

cnf(c_8756,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(renaming,[status(thm)],[c_8755])).

cnf(c_4101,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3878])).

cnf(c_4113,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3887])).

cnf(c_7412,plain,
    ( ~ v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7411])).

cnf(c_8593,plain,
    ( v5_pre_topc(sK6,sK3,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8592])).

cnf(c_35,plain,
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
    inference(cnf_transformation,[],[f127])).

cnf(c_17491,plain,
    ( v5_pre_topc(sK6,X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v5_pre_topc(sK6,X0,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_17503,plain,
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
    inference(instantiation,[status(thm)],[c_17491])).

cnf(c_42276,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8756,c_48,c_47,c_46,c_45,c_41,c_4101,c_4113,c_7412,c_8593,c_13023,c_17503])).

cnf(c_42277,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(renaming,[status(thm)],[c_42276])).

cnf(c_42278,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42277])).

cnf(c_50570,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46600,c_42278])).

cnf(c_50571,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_50570])).

cnf(c_50578,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14378,c_50571])).

cnf(c_50577,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3845,c_50571])).

cnf(c_57768,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7284,c_50577])).

cnf(c_57885,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_52530,c_133,c_15585,c_50578,c_51674,c_57768])).

cnf(c_57891,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14378,c_57885])).

cnf(c_61779,plain,
    ( sK6 = k1_xboole_0
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_52553,c_51675,c_57891])).

cnf(c_61785,plain,
    ( sK6 = k1_xboole_0
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7398,c_61779])).

cnf(c_62115,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_51621,c_52,c_61785])).

cnf(c_62127,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_62115,c_57885])).

cnf(c_28,plain,
    ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3837,plain,
    ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5731,plain,
    ( k1_relat_1(sK2(X0,X1)) = X0
    | v1_funct_2(sK2(X0,X1),X0,X1) != iProver_top
    | v1_funct_1(sK2(X0,X1)) != iProver_top
    | v1_relat_1(sK2(X0,X1)) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3837,c_3815])).

cnf(c_27,plain,
    ( v1_relat_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_85,plain,
    ( v1_relat_1(sK2(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,plain,
    ( v1_funct_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_91,plain,
    ( v1_funct_1(sK2(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,plain,
    ( v1_funct_2(sK2(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_94,plain,
    ( v1_funct_2(sK2(X0,X1),X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10580,plain,
    ( k1_relat_1(sK2(X0,X1)) = X0
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5731,c_85,c_91,c_94])).

cnf(c_10591,plain,
    ( k1_relat_1(sK2(X0,u1_struct_0(sK4))) = X0
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_10580,c_8212])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_14,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_14])).

cnf(c_265,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_3817,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_4962,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3827,c_3817])).

cnf(c_5150,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4962,c_57])).

cnf(c_5326,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5150,c_3846])).

cnf(c_5606,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5326,c_3846])).

cnf(c_10954,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | k1_relat_1(sK2(X0,u1_struct_0(sK4))) = X0 ),
    inference(superposition,[status(thm)],[c_10591,c_5606])).

cnf(c_24558,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | k1_relat_1(sK2(X0,u1_struct_0(sK4))) = X0
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10954,c_3826])).

cnf(c_5325,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK6)
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4708,c_3846])).

cnf(c_14340,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_14330,c_5325])).

cnf(c_14821,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))) = iProver_top
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_14340,c_3962])).

cnf(c_3831,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6466,plain,
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
    inference(superposition,[status(thm)],[c_3827,c_3831])).

cnf(c_73,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_75,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_76,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_78,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_4212,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_4213,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4212])).

cnf(c_4215,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4213])).

cnf(c_3830,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5724,plain,
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
    inference(superposition,[status(thm)],[c_3827,c_3830])).

cnf(c_4391,plain,
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
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_4392,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4391])).

cnf(c_6064,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5724,c_49,c_50,c_51,c_52,c_56,c_57,c_75,c_78,c_3878,c_3967,c_3887,c_4215,c_4392])).

cnf(c_6065,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6064])).

cnf(c_6942,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6466,c_49,c_50,c_51,c_52,c_56,c_57,c_75,c_78,c_3878,c_3967,c_3887,c_4215,c_4392,c_5724])).

cnf(c_6943,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6942])).

cnf(c_14809,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14340,c_6943])).

cnf(c_14822,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))) != iProver_top
    | v5_pre_topc(sK6,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_14340,c_3967])).

cnf(c_14825,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14340,c_3887])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_14833,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14825,c_7])).

cnf(c_6949,plain,
    ( v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3962,c_6943])).

cnf(c_14808,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14340,c_6949])).

cnf(c_14918,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14808,c_7])).

cnf(c_16875,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))) != iProver_top
    | u1_struct_0(sK3) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14809,c_14822,c_14833,c_14918])).

cnf(c_16876,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_16875])).

cnf(c_16882,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14821,c_16876])).

cnf(c_17127,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14340,c_16882])).

cnf(c_27062,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK6)
    | k1_relat_1(sK2(X0,u1_struct_0(sK4))) = X0
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_24558,c_17127])).

cnf(c_4437,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_2846])).

cnf(c_4616,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(instantiation,[status(thm)],[c_2846])).

cnf(c_5607,plain,
    ( ~ v1_xboole_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5606])).

cnf(c_5982,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2855,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_4277,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | X2 != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2855])).

cnf(c_4436,plain,
    ( v1_funct_2(sK6,X0,X1)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4277])).

cnf(c_5244,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4436])).

cnf(c_6147,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | sK6 != sK6
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_5244])).

cnf(c_6149,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | sK6 != sK6
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6147])).

cnf(c_8386,plain,
    ( ~ v1_relat_1(sK6)
    | v1_xboole_0(sK6)
    | u1_struct_0(sK3) = k1_relat_1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8379])).

cnf(c_15598,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7904])).

cnf(c_28396,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27062,c_57,c_5,c_4437,c_4616,c_5607,c_5982,c_6149,c_7154,c_8386,c_10697,c_15598,c_17127])).

cnf(c_28397,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK6)
    | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_28396])).

cnf(c_62212,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_62115,c_28397])).

cnf(c_8168,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0)
    | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | X0 != sK6
    | X2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2855])).

cnf(c_11186,plain,
    ( v1_funct_2(sK6,X0,X1)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0)
    | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | X1 != k1_xboole_0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_8168])).

cnf(c_12565,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0)
    | X0 != k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_11186])).

cnf(c_17533,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | u1_struct_0(sK4) != k1_xboole_0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_12565])).

cnf(c_46607,plain,
    ( sK6 = k1_xboole_0
    | v5_pre_topc(sK6,g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14378,c_6943])).

cnf(c_8652,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK6) ),
    inference(resolution,[status(thm)],[c_34,c_39])).

cnf(c_6944,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6943])).

cnf(c_8842,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8652,c_6944])).

cnf(c_8843,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) ),
    inference(renaming,[status(thm)],[c_8842])).

cnf(c_6066,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6065])).

cnf(c_6950,plain,
    ( v5_pre_topc(sK6,sK3,sK4)
    | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6949])).

cnf(c_17492,plain,
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
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_17499,plain,
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
    inference(instantiation,[status(thm)],[c_17492])).

cnf(c_42030,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8843,c_48,c_47,c_46,c_45,c_41,c_4101,c_4113,c_6066,c_6950,c_17499])).

cnf(c_42032,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42030])).

cnf(c_49069,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46607,c_42032])).

cnf(c_49077,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14378,c_49069])).

cnf(c_49075,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3845,c_49069])).

cnf(c_56051,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7284,c_49075])).

cnf(c_56068,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49077,c_133,c_15585,c_56051])).

cnf(c_56075,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_51595,c_56068])).

cnf(c_46618,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14378,c_3887])).

cnf(c_56256,plain,
    ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_56075,c_133,c_15585,c_46618,c_56051])).

cnf(c_56258,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_56256])).

cnf(c_62266,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_62115,c_14340])).

cnf(c_75806,plain,
    ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_62212,c_52,c_57,c_5,c_133,c_4437,c_4616,c_5607,c_5982,c_6149,c_15584,c_15585,c_15598,c_17534,c_46618,c_56051,c_56075,c_61785,c_62266])).

cnf(c_75807,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_75806])).

cnf(c_62130,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_62115,c_56256])).

cnf(c_97356,plain,
    ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_75807,c_62130])).

cnf(c_3847,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_5729,plain,
    ( m1_subset_1(sK2(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_3837])).

cnf(c_8214,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_3841])).

cnf(c_8353,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2(k1_xboole_0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5729,c_8214])).

cnf(c_10036,plain,
    ( v1_xboole_0(sK2(k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3847,c_8353])).

cnf(c_10069,plain,
    ( sK2(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10036,c_3846])).

cnf(c_3840,plain,
    ( v1_funct_2(sK2(X0,X1),X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10671,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10069,c_3840])).

cnf(c_98958,plain,
    ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_97356,c_10671])).

cnf(c_4963,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3887,c_3817])).

cnf(c_5142,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4963,c_3878])).

cnf(c_5324,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5142,c_3846])).

cnf(c_5483,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5324,c_3846])).

cnf(c_10955,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | k1_relat_1(sK2(X0,u1_struct_0(sK4))) = X0 ),
    inference(superposition,[status(thm)],[c_10591,c_5483])).

cnf(c_11872,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10069,c_10955])).

cnf(c_62311,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_62115,c_5483])).

cnf(c_64201,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_62311])).

cnf(c_67933,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11872,c_5,c_64201])).

cnf(c_67934,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_67933])).

cnf(c_4656,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3827,c_3815])).

cnf(c_4831,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4656,c_56,c_57])).

cnf(c_62321,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0)
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_62115,c_4831])).

cnf(c_3843,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5076,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_3843])).

cnf(c_71355,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_62321,c_5076])).

cnf(c_71362,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0)
    | u1_struct_0(sK3) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_67934,c_71355])).

cnf(c_5078,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5076])).

cnf(c_17534,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | u1_struct_0(sK4) != k1_xboole_0
    | sK6 != sK6
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17533])).

cnf(c_64210,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_62321])).

cnf(c_81699,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_71362,c_57,c_5,c_133,c_4437,c_4616,c_5078,c_5982,c_6149,c_15585,c_17534,c_46618,c_56051,c_56075,c_64201,c_64210])).

cnf(c_81700,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0)
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_81699])).

cnf(c_97354,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_81700,c_62130])).

cnf(c_98959,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_98958,c_97354])).

cnf(c_62328,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_62115,c_3878])).

cnf(c_99049,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_98958,c_62328])).

cnf(c_100396,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_98959,c_99049])).

cnf(c_102113,plain,
    ( u1_struct_0(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_100396,c_98958])).

cnf(c_104627,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_62127,c_102113])).

cnf(c_104630,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_104627,c_10671])).

cnf(c_104632,plain,
    ( l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7398,c_104630])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_104632,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 24.08/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.08/3.49  
% 24.08/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 24.08/3.49  
% 24.08/3.49  ------  iProver source info
% 24.08/3.49  
% 24.08/3.49  git: date: 2020-06-30 10:37:57 +0100
% 24.08/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 24.08/3.49  git: non_committed_changes: false
% 24.08/3.49  git: last_make_outside_of_git: false
% 24.08/3.49  
% 24.08/3.49  ------ 
% 24.08/3.49  ------ Parsing...
% 24.08/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 24.08/3.49  
% 24.08/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 24.08/3.49  
% 24.08/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 24.08/3.49  
% 24.08/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 24.08/3.49  ------ Proving...
% 24.08/3.49  ------ Problem Properties 
% 24.08/3.49  
% 24.08/3.49  
% 24.08/3.49  clauses                                 42
% 24.08/3.49  conjectures                             13
% 24.08/3.49  EPR                                     13
% 24.08/3.49  Horn                                    36
% 24.08/3.49  unary                                   19
% 24.08/3.49  binary                                  12
% 24.08/3.49  lits                                    113
% 24.08/3.49  lits eq                                 8
% 24.08/3.49  fd_pure                                 0
% 24.08/3.49  fd_pseudo                               0
% 24.08/3.49  fd_cond                                 2
% 24.08/3.49  fd_pseudo_cond                          1
% 24.08/3.49  AC symbols                              0
% 24.08/3.49  
% 24.08/3.49  ------ Input Options Time Limit: Unbounded
% 24.08/3.49  
% 24.08/3.49  
% 24.08/3.49  ------ 
% 24.08/3.49  Current options:
% 24.08/3.49  ------ 
% 24.08/3.49  
% 24.08/3.49  
% 24.08/3.49  
% 24.08/3.49  
% 24.08/3.49  ------ Proving...
% 24.08/3.49  
% 24.08/3.49  
% 24.08/3.49  % SZS status Theorem for theBenchmark.p
% 24.08/3.49  
% 24.08/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 24.08/3.49  
% 24.08/3.49  fof(f17,axiom,(
% 24.08/3.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f40,plain,(
% 24.08/3.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.08/3.49    inference(ennf_transformation,[],[f17])).
% 24.08/3.49  
% 24.08/3.49  fof(f102,plain,(
% 24.08/3.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f40])).
% 24.08/3.49  
% 24.08/3.49  fof(f16,axiom,(
% 24.08/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f24,plain,(
% 24.08/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 24.08/3.49    inference(pure_predicate_removal,[],[f16])).
% 24.08/3.49  
% 24.08/3.49  fof(f39,plain,(
% 24.08/3.49    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 24.08/3.49    inference(ennf_transformation,[],[f24])).
% 24.08/3.49  
% 24.08/3.49  fof(f101,plain,(
% 24.08/3.49    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 24.08/3.49    inference(cnf_transformation,[],[f39])).
% 24.08/3.49  
% 24.08/3.49  fof(f21,conjecture,(
% 24.08/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f22,negated_conjecture,(
% 24.08/3.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 24.08/3.49    inference(negated_conjecture,[],[f21])).
% 24.08/3.49  
% 24.08/3.49  fof(f47,plain,(
% 24.08/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 24.08/3.49    inference(ennf_transformation,[],[f22])).
% 24.08/3.49  
% 24.08/3.49  fof(f48,plain,(
% 24.08/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 24.08/3.49    inference(flattening,[],[f47])).
% 24.08/3.49  
% 24.08/3.49  fof(f65,plain,(
% 24.08/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 24.08/3.49    inference(nnf_transformation,[],[f48])).
% 24.08/3.49  
% 24.08/3.49  fof(f66,plain,(
% 24.08/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 24.08/3.49    inference(flattening,[],[f65])).
% 24.08/3.49  
% 24.08/3.49  fof(f70,plain,(
% 24.08/3.49    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK6 = X2 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK6))) )),
% 24.08/3.49    introduced(choice_axiom,[])).
% 24.08/3.49  
% 24.08/3.49  fof(f69,plain,(
% 24.08/3.49    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK5,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK5,X0,X1)) & sK5 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 24.08/3.49    introduced(choice_axiom,[])).
% 24.08/3.49  
% 24.08/3.49  fof(f68,plain,(
% 24.08/3.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(X2,X0,sK4)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(X2,X0,sK4)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4)) & v1_funct_1(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))) )),
% 24.08/3.49    introduced(choice_axiom,[])).
% 24.08/3.49  
% 24.08/3.49  fof(f67,plain,(
% 24.08/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK3,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK3,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 24.08/3.49    introduced(choice_axiom,[])).
% 24.08/3.49  
% 24.08/3.49  fof(f71,plain,(
% 24.08/3.49    ((((~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(sK5,sK3,sK4)) & (v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,sK3,sK4)) & sK5 = sK6 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 24.08/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f66,f70,f69,f68,f67])).
% 24.08/3.49  
% 24.08/3.49  fof(f114,plain,(
% 24.08/3.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 24.08/3.49    inference(cnf_transformation,[],[f71])).
% 24.08/3.49  
% 24.08/3.49  fof(f118,plain,(
% 24.08/3.49    sK5 = sK6),
% 24.08/3.49    inference(cnf_transformation,[],[f71])).
% 24.08/3.49  
% 24.08/3.49  fof(f6,axiom,(
% 24.08/3.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f59,plain,(
% 24.08/3.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 24.08/3.49    inference(nnf_transformation,[],[f6])).
% 24.08/3.49  
% 24.08/3.49  fof(f82,plain,(
% 24.08/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 24.08/3.49    inference(cnf_transformation,[],[f59])).
% 24.08/3.49  
% 24.08/3.49  fof(f7,axiom,(
% 24.08/3.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f29,plain,(
% 24.08/3.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 24.08/3.49    inference(ennf_transformation,[],[f7])).
% 24.08/3.49  
% 24.08/3.49  fof(f84,plain,(
% 24.08/3.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f29])).
% 24.08/3.49  
% 24.08/3.49  fof(f83,plain,(
% 24.08/3.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f59])).
% 24.08/3.49  
% 24.08/3.49  fof(f8,axiom,(
% 24.08/3.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f85,plain,(
% 24.08/3.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 24.08/3.49    inference(cnf_transformation,[],[f8])).
% 24.08/3.49  
% 24.08/3.49  fof(f12,axiom,(
% 24.08/3.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f33,plain,(
% 24.08/3.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 24.08/3.49    inference(ennf_transformation,[],[f12])).
% 24.08/3.49  
% 24.08/3.49  fof(f34,plain,(
% 24.08/3.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 24.08/3.49    inference(flattening,[],[f33])).
% 24.08/3.49  
% 24.08/3.49  fof(f90,plain,(
% 24.08/3.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f34])).
% 24.08/3.49  
% 24.08/3.49  fof(f14,axiom,(
% 24.08/3.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f37,plain,(
% 24.08/3.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 24.08/3.49    inference(ennf_transformation,[],[f14])).
% 24.08/3.49  
% 24.08/3.49  fof(f38,plain,(
% 24.08/3.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 24.08/3.49    inference(flattening,[],[f37])).
% 24.08/3.49  
% 24.08/3.49  fof(f60,plain,(
% 24.08/3.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 24.08/3.49    inference(nnf_transformation,[],[f38])).
% 24.08/3.49  
% 24.08/3.49  fof(f94,plain,(
% 24.08/3.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f60])).
% 24.08/3.49  
% 24.08/3.49  fof(f10,axiom,(
% 24.08/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f25,plain,(
% 24.08/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 24.08/3.49    inference(pure_predicate_removal,[],[f10])).
% 24.08/3.49  
% 24.08/3.49  fof(f31,plain,(
% 24.08/3.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 24.08/3.49    inference(ennf_transformation,[],[f25])).
% 24.08/3.49  
% 24.08/3.49  fof(f87,plain,(
% 24.08/3.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 24.08/3.49    inference(cnf_transformation,[],[f31])).
% 24.08/3.49  
% 24.08/3.49  fof(f115,plain,(
% 24.08/3.49    v1_funct_1(sK6)),
% 24.08/3.49    inference(cnf_transformation,[],[f71])).
% 24.08/3.49  
% 24.08/3.49  fof(f113,plain,(
% 24.08/3.49    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))),
% 24.08/3.49    inference(cnf_transformation,[],[f71])).
% 24.08/3.49  
% 24.08/3.49  fof(f11,axiom,(
% 24.08/3.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f32,plain,(
% 24.08/3.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 24.08/3.49    inference(ennf_transformation,[],[f11])).
% 24.08/3.49  
% 24.08/3.49  fof(f88,plain,(
% 24.08/3.49    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f32])).
% 24.08/3.49  
% 24.08/3.49  fof(f4,axiom,(
% 24.08/3.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f28,plain,(
% 24.08/3.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 24.08/3.49    inference(ennf_transformation,[],[f4])).
% 24.08/3.49  
% 24.08/3.49  fof(f78,plain,(
% 24.08/3.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f28])).
% 24.08/3.49  
% 24.08/3.49  fof(f117,plain,(
% 24.08/3.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),
% 24.08/3.49    inference(cnf_transformation,[],[f71])).
% 24.08/3.49  
% 24.08/3.49  fof(f116,plain,(
% 24.08/3.49    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),
% 24.08/3.49    inference(cnf_transformation,[],[f71])).
% 24.08/3.49  
% 24.08/3.49  fof(f18,axiom,(
% 24.08/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f23,plain,(
% 24.08/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 24.08/3.49    inference(pure_predicate_removal,[],[f18])).
% 24.08/3.49  
% 24.08/3.49  fof(f41,plain,(
% 24.08/3.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 24.08/3.49    inference(ennf_transformation,[],[f23])).
% 24.08/3.49  
% 24.08/3.49  fof(f42,plain,(
% 24.08/3.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 24.08/3.49    inference(flattening,[],[f41])).
% 24.08/3.49  
% 24.08/3.49  fof(f103,plain,(
% 24.08/3.49    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f42])).
% 24.08/3.49  
% 24.08/3.49  fof(f111,plain,(
% 24.08/3.49    l1_pre_topc(sK4)),
% 24.08/3.49    inference(cnf_transformation,[],[f71])).
% 24.08/3.49  
% 24.08/3.49  fof(f119,plain,(
% 24.08/3.49    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | v5_pre_topc(sK5,sK3,sK4)),
% 24.08/3.49    inference(cnf_transformation,[],[f71])).
% 24.08/3.49  
% 24.08/3.49  fof(f19,axiom,(
% 24.08/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f43,plain,(
% 24.08/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 24.08/3.49    inference(ennf_transformation,[],[f19])).
% 24.08/3.49  
% 24.08/3.49  fof(f44,plain,(
% 24.08/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 24.08/3.49    inference(flattening,[],[f43])).
% 24.08/3.49  
% 24.08/3.49  fof(f63,plain,(
% 24.08/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 24.08/3.49    inference(nnf_transformation,[],[f44])).
% 24.08/3.49  
% 24.08/3.49  fof(f105,plain,(
% 24.08/3.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f63])).
% 24.08/3.49  
% 24.08/3.49  fof(f124,plain,(
% 24.08/3.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 24.08/3.49    inference(equality_resolution,[],[f105])).
% 24.08/3.49  
% 24.08/3.49  fof(f108,plain,(
% 24.08/3.49    v2_pre_topc(sK3)),
% 24.08/3.49    inference(cnf_transformation,[],[f71])).
% 24.08/3.49  
% 24.08/3.49  fof(f109,plain,(
% 24.08/3.49    l1_pre_topc(sK3)),
% 24.08/3.49    inference(cnf_transformation,[],[f71])).
% 24.08/3.49  
% 24.08/3.49  fof(f110,plain,(
% 24.08/3.49    v2_pre_topc(sK4)),
% 24.08/3.49    inference(cnf_transformation,[],[f71])).
% 24.08/3.49  
% 24.08/3.49  fof(f120,plain,(
% 24.08/3.49    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~v5_pre_topc(sK5,sK3,sK4)),
% 24.08/3.49    inference(cnf_transformation,[],[f71])).
% 24.08/3.49  
% 24.08/3.49  fof(f20,axiom,(
% 24.08/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f45,plain,(
% 24.08/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 24.08/3.49    inference(ennf_transformation,[],[f20])).
% 24.08/3.49  
% 24.08/3.49  fof(f46,plain,(
% 24.08/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 24.08/3.49    inference(flattening,[],[f45])).
% 24.08/3.49  
% 24.08/3.49  fof(f64,plain,(
% 24.08/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 24.08/3.49    inference(nnf_transformation,[],[f46])).
% 24.08/3.49  
% 24.08/3.49  fof(f107,plain,(
% 24.08/3.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f64])).
% 24.08/3.49  
% 24.08/3.49  fof(f126,plain,(
% 24.08/3.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 24.08/3.49    inference(equality_resolution,[],[f107])).
% 24.08/3.49  
% 24.08/3.49  fof(f3,axiom,(
% 24.08/3.49    v1_xboole_0(k1_xboole_0)),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f77,plain,(
% 24.08/3.49    v1_xboole_0(k1_xboole_0)),
% 24.08/3.49    inference(cnf_transformation,[],[f3])).
% 24.08/3.49  
% 24.08/3.49  fof(f2,axiom,(
% 24.08/3.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f27,plain,(
% 24.08/3.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 24.08/3.49    inference(ennf_transformation,[],[f2])).
% 24.08/3.49  
% 24.08/3.49  fof(f53,plain,(
% 24.08/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 24.08/3.49    inference(nnf_transformation,[],[f27])).
% 24.08/3.49  
% 24.08/3.49  fof(f54,plain,(
% 24.08/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 24.08/3.49    inference(rectify,[],[f53])).
% 24.08/3.49  
% 24.08/3.49  fof(f55,plain,(
% 24.08/3.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 24.08/3.49    introduced(choice_axiom,[])).
% 24.08/3.49  
% 24.08/3.49  fof(f56,plain,(
% 24.08/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 24.08/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f54,f55])).
% 24.08/3.49  
% 24.08/3.49  fof(f75,plain,(
% 24.08/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f56])).
% 24.08/3.49  
% 24.08/3.49  fof(f1,axiom,(
% 24.08/3.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f49,plain,(
% 24.08/3.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 24.08/3.49    inference(nnf_transformation,[],[f1])).
% 24.08/3.49  
% 24.08/3.49  fof(f50,plain,(
% 24.08/3.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 24.08/3.49    inference(rectify,[],[f49])).
% 24.08/3.49  
% 24.08/3.49  fof(f51,plain,(
% 24.08/3.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 24.08/3.49    introduced(choice_axiom,[])).
% 24.08/3.49  
% 24.08/3.49  fof(f52,plain,(
% 24.08/3.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 24.08/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).
% 24.08/3.49  
% 24.08/3.49  fof(f72,plain,(
% 24.08/3.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f52])).
% 24.08/3.49  
% 24.08/3.49  fof(f104,plain,(
% 24.08/3.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f63])).
% 24.08/3.49  
% 24.08/3.49  fof(f125,plain,(
% 24.08/3.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 24.08/3.49    inference(equality_resolution,[],[f104])).
% 24.08/3.49  
% 24.08/3.49  fof(f106,plain,(
% 24.08/3.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f64])).
% 24.08/3.49  
% 24.08/3.49  fof(f127,plain,(
% 24.08/3.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 24.08/3.49    inference(equality_resolution,[],[f106])).
% 24.08/3.49  
% 24.08/3.49  fof(f15,axiom,(
% 24.08/3.49    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f26,plain,(
% 24.08/3.49    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 24.08/3.49    inference(pure_predicate_removal,[],[f15])).
% 24.08/3.49  
% 24.08/3.49  fof(f61,plain,(
% 24.08/3.49    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK2(X0,X1),X0,X1) & v1_funct_1(sK2(X0,X1)) & v4_relat_1(sK2(X0,X1),X0) & v1_relat_1(sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 24.08/3.49    introduced(choice_axiom,[])).
% 24.08/3.49  
% 24.08/3.49  fof(f62,plain,(
% 24.08/3.49    ! [X0,X1] : (v1_funct_2(sK2(X0,X1),X0,X1) & v1_funct_1(sK2(X0,X1)) & v4_relat_1(sK2(X0,X1),X0) & v1_relat_1(sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 24.08/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f61])).
% 24.08/3.49  
% 24.08/3.49  fof(f96,plain,(
% 24.08/3.49    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 24.08/3.49    inference(cnf_transformation,[],[f62])).
% 24.08/3.49  
% 24.08/3.49  fof(f97,plain,(
% 24.08/3.49    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1))) )),
% 24.08/3.49    inference(cnf_transformation,[],[f62])).
% 24.08/3.49  
% 24.08/3.49  fof(f99,plain,(
% 24.08/3.49    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1))) )),
% 24.08/3.49    inference(cnf_transformation,[],[f62])).
% 24.08/3.49  
% 24.08/3.49  fof(f100,plain,(
% 24.08/3.49    ( ! [X0,X1] : (v1_funct_2(sK2(X0,X1),X0,X1)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f62])).
% 24.08/3.49  
% 24.08/3.49  fof(f13,axiom,(
% 24.08/3.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f35,plain,(
% 24.08/3.49    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 24.08/3.49    inference(ennf_transformation,[],[f13])).
% 24.08/3.49  
% 24.08/3.49  fof(f36,plain,(
% 24.08/3.49    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 24.08/3.49    inference(flattening,[],[f35])).
% 24.08/3.49  
% 24.08/3.49  fof(f92,plain,(
% 24.08/3.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f36])).
% 24.08/3.49  
% 24.08/3.49  fof(f9,axiom,(
% 24.08/3.49    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f30,plain,(
% 24.08/3.49    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 24.08/3.49    inference(ennf_transformation,[],[f9])).
% 24.08/3.49  
% 24.08/3.49  fof(f86,plain,(
% 24.08/3.49    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 24.08/3.49    inference(cnf_transformation,[],[f30])).
% 24.08/3.49  
% 24.08/3.49  fof(f5,axiom,(
% 24.08/3.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 24.08/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 24.08/3.49  
% 24.08/3.49  fof(f57,plain,(
% 24.08/3.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 24.08/3.49    inference(nnf_transformation,[],[f5])).
% 24.08/3.49  
% 24.08/3.49  fof(f58,plain,(
% 24.08/3.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 24.08/3.49    inference(flattening,[],[f57])).
% 24.08/3.49  
% 24.08/3.49  fof(f81,plain,(
% 24.08/3.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 24.08/3.49    inference(cnf_transformation,[],[f58])).
% 24.08/3.49  
% 24.08/3.49  fof(f121,plain,(
% 24.08/3.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 24.08/3.49    inference(equality_resolution,[],[f81])).
% 24.08/3.49  
% 24.08/3.49  fof(f80,plain,(
% 24.08/3.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 24.08/3.49    inference(cnf_transformation,[],[f58])).
% 24.08/3.49  
% 24.08/3.49  fof(f122,plain,(
% 24.08/3.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 24.08/3.49    inference(equality_resolution,[],[f80])).
% 24.08/3.49  
% 24.08/3.49  cnf(c_30,plain,
% 24.08/3.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 24.08/3.49      | ~ l1_pre_topc(X0) ),
% 24.08/3.49      inference(cnf_transformation,[],[f102]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3835,plain,
% 24.08/3.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 24.08/3.49      | l1_pre_topc(X0) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_29,plain,
% 24.08/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 24.08/3.49      inference(cnf_transformation,[],[f101]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3836,plain,
% 24.08/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7398,plain,
% 24.08/3.49      ( l1_pre_topc(X0) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3835,c_3836]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_42,negated_conjecture,
% 24.08/3.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
% 24.08/3.49      inference(cnf_transformation,[],[f114]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3824,plain,
% 24.08/3.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_38,negated_conjecture,
% 24.08/3.49      ( sK5 = sK6 ),
% 24.08/3.49      inference(cnf_transformation,[],[f118]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3887,plain,
% 24.08/3.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 24.08/3.49      inference(light_normalisation,[status(thm)],[c_3824,c_38]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_11,plain,
% 24.08/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 24.08/3.49      inference(cnf_transformation,[],[f82]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3844,plain,
% 24.08/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 24.08/3.49      | r1_tarski(X0,X1) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6674,plain,
% 24.08/3.49      ( r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3887,c_3844]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_12,plain,
% 24.08/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 24.08/3.49      | ~ v1_relat_1(X1)
% 24.08/3.49      | v1_relat_1(X0) ),
% 24.08/3.49      inference(cnf_transformation,[],[f84]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_10,plain,
% 24.08/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 24.08/3.49      inference(cnf_transformation,[],[f83]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_340,plain,
% 24.08/3.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 24.08/3.49      inference(prop_impl,[status(thm)],[c_10]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_341,plain,
% 24.08/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_340]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_427,plain,
% 24.08/3.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 24.08/3.49      inference(bin_hyper_res,[status(thm)],[c_12,c_341]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3816,plain,
% 24.08/3.49      ( r1_tarski(X0,X1) != iProver_top
% 24.08/3.49      | v1_relat_1(X1) != iProver_top
% 24.08/3.49      | v1_relat_1(X0) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_13723,plain,
% 24.08/3.49      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) != iProver_top
% 24.08/3.49      | v1_relat_1(sK6) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_6674,c_3816]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_2847,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_2846,plain,( X0 = X0 ),theory(equality) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6901,plain,
% 24.08/3.49      ( X0 != X1 | X1 = X0 ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_2847,c_2846]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7143,plain,
% 24.08/3.49      ( sK6 = sK5 ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_6901,c_38]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_2853,plain,
% 24.08/3.49      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 24.08/3.49      theory(equality) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7154,plain,
% 24.08/3.49      ( ~ v1_relat_1(sK5) | v1_relat_1(sK6) ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_7143,c_2853]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7160,plain,
% 24.08/3.49      ( v1_relat_1(sK5) != iProver_top | v1_relat_1(sK6) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_7154]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4675,plain,
% 24.08/3.49      ( r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_11,c_42]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_10265,plain,
% 24.08/3.49      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))
% 24.08/3.49      | v1_relat_1(sK5) ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_427,c_4675]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_13,plain,
% 24.08/3.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 24.08/3.49      inference(cnf_transformation,[],[f85]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_10697,plain,
% 24.08/3.49      ( v1_relat_1(sK5) ),
% 24.08/3.49      inference(forward_subsumption_resolution,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_10265,c_13]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_10698,plain,
% 24.08/3.49      ( v1_relat_1(sK5) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_10697]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_14330,plain,
% 24.08/3.49      ( v1_relat_1(sK6) = iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_13723,c_7160,c_10698]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_17,plain,
% 24.08/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 24.08/3.49      | v1_partfun1(X0,X1)
% 24.08/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 24.08/3.49      | ~ v1_funct_1(X0)
% 24.08/3.49      | v1_xboole_0(X2) ),
% 24.08/3.49      inference(cnf_transformation,[],[f90]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_23,plain,
% 24.08/3.49      ( ~ v1_partfun1(X0,X1)
% 24.08/3.49      | ~ v4_relat_1(X0,X1)
% 24.08/3.49      | ~ v1_relat_1(X0)
% 24.08/3.49      | k1_relat_1(X0) = X1 ),
% 24.08/3.49      inference(cnf_transformation,[],[f94]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_654,plain,
% 24.08/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 24.08/3.49      | ~ v4_relat_1(X0,X1)
% 24.08/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 24.08/3.49      | ~ v1_funct_1(X0)
% 24.08/3.49      | ~ v1_relat_1(X0)
% 24.08/3.49      | v1_xboole_0(X2)
% 24.08/3.49      | k1_relat_1(X0) = X1 ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_17,c_23]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_15,plain,
% 24.08/3.49      ( v4_relat_1(X0,X1)
% 24.08/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 24.08/3.49      inference(cnf_transformation,[],[f87]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_658,plain,
% 24.08/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 24.08/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 24.08/3.49      | ~ v1_funct_1(X0)
% 24.08/3.49      | ~ v1_relat_1(X0)
% 24.08/3.49      | v1_xboole_0(X2)
% 24.08/3.49      | k1_relat_1(X0) = X1 ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_654,c_15]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3815,plain,
% 24.08/3.49      ( k1_relat_1(X0) = X1
% 24.08/3.49      | v1_funct_2(X0,X1,X2) != iProver_top
% 24.08/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 24.08/3.49      | v1_funct_1(X0) != iProver_top
% 24.08/3.49      | v1_relat_1(X0) != iProver_top
% 24.08/3.49      | v1_xboole_0(X2) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4305,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | v1_funct_1(sK6) != iProver_top
% 24.08/3.49      | v1_relat_1(sK6) != iProver_top
% 24.08/3.49      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3887,c_3815]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_41,negated_conjecture,
% 24.08/3.49      ( v1_funct_1(sK6) ),
% 24.08/3.49      inference(cnf_transformation,[],[f115]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_56,plain,
% 24.08/3.49      ( v1_funct_1(sK6) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_43,negated_conjecture,
% 24.08/3.49      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 24.08/3.49      inference(cnf_transformation,[],[f113]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3823,plain,
% 24.08/3.49      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3878,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 24.08/3.49      inference(light_normalisation,[status(thm)],[c_3823,c_38]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4708,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | v1_relat_1(sK6) != iProver_top
% 24.08/3.49      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_4305,c_56,c_3878]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_16,plain,
% 24.08/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 24.08/3.49      | ~ v1_xboole_0(X2)
% 24.08/3.49      | v1_xboole_0(X0) ),
% 24.08/3.49      inference(cnf_transformation,[],[f88]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3841,plain,
% 24.08/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 24.08/3.49      | v1_xboole_0(X2) != iProver_top
% 24.08/3.49      | v1_xboole_0(X0) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8212,plain,
% 24.08/3.49      ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | v1_xboole_0(sK6) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3887,c_3841]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8379,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | v1_relat_1(sK6) != iProver_top
% 24.08/3.49      | v1_xboole_0(sK6) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_4708,c_8212]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_14338,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | v1_xboole_0(sK6) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14330,c_8379]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6,plain,
% 24.08/3.49      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 24.08/3.49      inference(cnf_transformation,[],[f78]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3846,plain,
% 24.08/3.49      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_14378,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6) | sK6 = k1_xboole_0 ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14338,c_3846]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_39,negated_conjecture,
% 24.08/3.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
% 24.08/3.49      inference(cnf_transformation,[],[f117]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3827,plain,
% 24.08/3.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_46616,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14378,c_3827]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_48796,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 24.08/3.49      | sK6 = k1_xboole_0
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | v1_funct_1(sK6) != iProver_top
% 24.08/3.49      | v1_relat_1(sK6) != iProver_top
% 24.08/3.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_46616,c_3815]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7151,plain,
% 24.08/3.49      ( X0 != sK5 | sK6 = X0 ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_7143,c_2847]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7804,plain,
% 24.08/3.49      ( ~ v1_xboole_0(sK5) | sK6 = k1_xboole_0 ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_7151,c_6]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_2852,plain,
% 24.08/3.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 24.08/3.49      theory(equality) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7447,plain,
% 24.08/3.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_2852,c_2846]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_17054,plain,
% 24.08/3.49      ( m1_subset_1(sK5,X0) | ~ m1_subset_1(sK6,X0) ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_7447,c_38]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_17169,plain,
% 24.08/3.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0)) | r1_tarski(sK5,X0) ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_17054,c_11]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_17937,plain,
% 24.08/3.49      ( r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_17169,c_39]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6810,plain,
% 24.08/3.49      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 24.08/3.49      | ~ v1_xboole_0(X2)
% 24.08/3.49      | v1_xboole_0(X0) ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_16,c_10]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_18631,plain,
% 24.08/3.49      ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | v1_xboole_0(sK5) ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_17937,c_6810]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_40,negated_conjecture,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
% 24.08/3.49      inference(cnf_transformation,[],[f116]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3826,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_46617,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14378,c_3826]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_47652,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | sK6 = k1_xboole_0 ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_46617]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_48865,plain,
% 24.08/3.49      ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ v1_funct_1(sK6)
% 24.08/3.49      | ~ v1_relat_1(sK6)
% 24.08/3.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 24.08/3.49      | sK6 = k1_xboole_0 ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_48796]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_51595,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 24.08/3.49      | sK6 = k1_xboole_0 ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_48796,c_41,c_7154,c_7804,c_10697,c_18631,c_47652,
% 24.08/3.49                 c_48865]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_31,plain,
% 24.08/3.49      ( ~ v2_pre_topc(X0)
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 24.08/3.49      | ~ l1_pre_topc(X0) ),
% 24.08/3.49      inference(cnf_transformation,[],[f103]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3834,plain,
% 24.08/3.49      ( v2_pre_topc(X0) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 24.08/3.49      | l1_pre_topc(X0) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_51621,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))))) = iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_51595,c_3834]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_45,negated_conjecture,
% 24.08/3.49      ( l1_pre_topc(sK4) ),
% 24.08/3.49      inference(cnf_transformation,[],[f111]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_52,plain,
% 24.08/3.49      ( l1_pre_topc(sK4) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_37,negated_conjecture,
% 24.08/3.49      ( v5_pre_topc(sK5,sK3,sK4)
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 24.08/3.49      inference(cnf_transformation,[],[f119]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3828,plain,
% 24.08/3.49      ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3962,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
% 24.08/3.49      inference(light_normalisation,[status(thm)],[c_3828,c_38]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_32,plain,
% 24.08/3.49      ( v5_pre_topc(X0,X1,X2)
% 24.08/3.49      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 24.08/3.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 24.08/3.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 24.08/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 24.08/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 24.08/3.49      | ~ v2_pre_topc(X1)
% 24.08/3.49      | ~ v2_pre_topc(X2)
% 24.08/3.49      | ~ l1_pre_topc(X1)
% 24.08/3.49      | ~ l1_pre_topc(X2)
% 24.08/3.49      | ~ v1_funct_1(X0) ),
% 24.08/3.49      inference(cnf_transformation,[],[f124]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3833,plain,
% 24.08/3.49      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 24.08/3.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 24.08/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 24.08/3.49      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 24.08/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 24.08/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 24.08/3.49      | v2_pre_topc(X1) != iProver_top
% 24.08/3.49      | v2_pre_topc(X2) != iProver_top
% 24.08/3.49      | l1_pre_topc(X1) != iProver_top
% 24.08/3.49      | l1_pre_topc(X2) != iProver_top
% 24.08/3.49      | v1_funct_1(X0) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8019,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v2_pre_topc(sK3) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(sK3) != iProver_top
% 24.08/3.49      | v1_funct_1(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3827,c_3833]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_48,negated_conjecture,
% 24.08/3.49      ( v2_pre_topc(sK3) ),
% 24.08/3.49      inference(cnf_transformation,[],[f108]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_49,plain,
% 24.08/3.49      ( v2_pre_topc(sK3) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_47,negated_conjecture,
% 24.08/3.49      ( l1_pre_topc(sK3) ),
% 24.08/3.49      inference(cnf_transformation,[],[f109]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_50,plain,
% 24.08/3.49      ( l1_pre_topc(sK3) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_46,negated_conjecture,
% 24.08/3.49      ( v2_pre_topc(sK4) ),
% 24.08/3.49      inference(cnf_transformation,[],[f110]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_51,plain,
% 24.08/3.49      ( v2_pre_topc(sK4) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_57,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_36,negated_conjecture,
% 24.08/3.49      ( ~ v5_pre_topc(sK5,sK3,sK4)
% 24.08/3.49      | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 24.08/3.49      inference(cnf_transformation,[],[f120]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3829,plain,
% 24.08/3.49      ( v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3967,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) != iProver_top ),
% 24.08/3.49      inference(light_normalisation,[status(thm)],[c_3829,c_38]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_34,plain,
% 24.08/3.49      ( v5_pre_topc(X0,X1,X2)
% 24.08/3.49      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 24.08/3.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 24.08/3.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 24.08/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 24.08/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 24.08/3.49      | ~ v2_pre_topc(X1)
% 24.08/3.49      | ~ v2_pre_topc(X2)
% 24.08/3.49      | ~ l1_pre_topc(X1)
% 24.08/3.49      | ~ l1_pre_topc(X2)
% 24.08/3.49      | ~ v1_funct_1(X0) ),
% 24.08/3.49      inference(cnf_transformation,[],[f126]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4346,plain,
% 24.08/3.49      ( ~ v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 24.08/3.49      | ~ v2_pre_topc(sK4)
% 24.08/3.49      | ~ v2_pre_topc(sK3)
% 24.08/3.49      | ~ l1_pre_topc(sK4)
% 24.08/3.49      | ~ l1_pre_topc(sK3)
% 24.08/3.49      | ~ v1_funct_1(sK6) ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_34]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4347,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 24.08/3.49      | v2_pre_topc(sK4) != iProver_top
% 24.08/3.49      | v2_pre_topc(sK3) != iProver_top
% 24.08/3.49      | l1_pre_topc(sK4) != iProver_top
% 24.08/3.49      | l1_pre_topc(sK3) != iProver_top
% 24.08/3.49      | v1_funct_1(sK6) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_4346]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8583,plain,
% 24.08/3.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_8019,c_49,c_50,c_51,c_52,c_56,c_57,c_3878,c_3967,
% 24.08/3.49                 c_3887,c_4347]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8584,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_8583]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8592,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3962,c_8584]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_46599,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14378,c_8592]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5,plain,
% 24.08/3.49      ( v1_xboole_0(k1_xboole_0) ),
% 24.08/3.49      inference(cnf_transformation,[],[f77]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_133,plain,
% 24.08/3.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3,plain,
% 24.08/3.49      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 24.08/3.49      inference(cnf_transformation,[],[f75]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3849,plain,
% 24.08/3.49      ( r1_tarski(X0,X1) = iProver_top
% 24.08/3.49      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_1,plain,
% 24.08/3.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 24.08/3.49      inference(cnf_transformation,[],[f72]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3851,plain,
% 24.08/3.49      ( r2_hidden(X0,X1) != iProver_top
% 24.08/3.49      | v1_xboole_0(X1) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7284,plain,
% 24.08/3.49      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3849,c_3851]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3845,plain,
% 24.08/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 24.08/3.49      | r1_tarski(X0,X1) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8723,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3845,c_8592]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8839,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_xboole_0(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_7284,c_8723]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_13023,plain,
% 24.08/3.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ v2_pre_topc(sK4)
% 24.08/3.49      | ~ l1_pre_topc(sK4) ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_31]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_13024,plain,
% 24.08/3.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 24.08/3.49      | v2_pre_topc(sK4) != iProver_top
% 24.08/3.49      | l1_pre_topc(sK4) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_13023]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_2848,plain,
% 24.08/3.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 24.08/3.49      theory(equality) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7904,plain,
% 24.08/3.49      ( v1_xboole_0(X0)
% 24.08/3.49      | ~ v1_xboole_0(k1_xboole_0)
% 24.08/3.49      | X0 != k1_xboole_0 ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_2848]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_15584,plain,
% 24.08/3.49      ( v1_xboole_0(sK6)
% 24.08/3.49      | ~ v1_xboole_0(k1_xboole_0)
% 24.08/3.49      | sK6 != k1_xboole_0 ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_7904]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_15585,plain,
% 24.08/3.49      ( sK6 != k1_xboole_0
% 24.08/3.49      | v1_xboole_0(sK6) = iProver_top
% 24.08/3.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_15584]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_46596,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14378,c_8723]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6673,plain,
% 24.08/3.49      ( r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3827,c_3844]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_46608,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14378,c_6673]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_51672,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_51595,c_46608]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_52546,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_46599,c_51,c_52,c_133,c_8839,c_13024,c_15585,c_46596,
% 24.08/3.49                 c_51672]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_52553,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14378,c_52546]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_51675,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_51595,c_46617]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_51674,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_51595,c_46616]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_33,plain,
% 24.08/3.49      ( ~ v5_pre_topc(X0,X1,X2)
% 24.08/3.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 24.08/3.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 24.08/3.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 24.08/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 24.08/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 24.08/3.49      | ~ v2_pre_topc(X1)
% 24.08/3.49      | ~ v2_pre_topc(X2)
% 24.08/3.49      | ~ l1_pre_topc(X1)
% 24.08/3.49      | ~ l1_pre_topc(X2)
% 24.08/3.49      | ~ v1_funct_1(X0) ),
% 24.08/3.49      inference(cnf_transformation,[],[f125]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3832,plain,
% 24.08/3.49      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 24.08/3.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 24.08/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 24.08/3.49      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 24.08/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 24.08/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 24.08/3.49      | v2_pre_topc(X1) != iProver_top
% 24.08/3.49      | v2_pre_topc(X2) != iProver_top
% 24.08/3.49      | l1_pre_topc(X1) != iProver_top
% 24.08/3.49      | l1_pre_topc(X2) != iProver_top
% 24.08/3.49      | v1_funct_1(X0) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7211,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v2_pre_topc(sK3) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(sK3) != iProver_top
% 24.08/3.49      | v1_funct_1(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3827,c_3832]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7410,plain,
% 24.08/3.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_7211,c_49,c_50,c_51,c_52,c_56,c_57,c_3878,c_3967,
% 24.08/3.49                 c_3887,c_4347]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7411,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_7410]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_46602,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14378,c_7411]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7419,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3845,c_7411]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7857,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_xboole_0(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_7284,c_7419]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_50353,plain,
% 24.08/3.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_46602,c_51,c_52,c_133,c_7857,c_13024,c_15585]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_50354,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_50353]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_52530,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_51674,c_50354]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_46600,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14378,c_8584]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8465,plain,
% 24.08/3.49      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 24.08/3.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ v2_pre_topc(sK3)
% 24.08/3.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ l1_pre_topc(sK3)
% 24.08/3.49      | ~ v1_funct_1(sK6) ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_32,c_39]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8585,plain,
% 24.08/3.49      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 24.08/3.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_8584]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8755,plain,
% 24.08/3.49      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_8465,c_8585]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8756,plain,
% 24.08/3.49      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 24.08/3.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_8755]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4101,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_3878]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4113,plain,
% 24.08/3.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_3887]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7412,plain,
% 24.08/3.49      ( ~ v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 24.08/3.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_7411]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8593,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,sK3,sK4)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 24.08/3.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_8592]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_35,plain,
% 24.08/3.49      ( ~ v5_pre_topc(X0,X1,X2)
% 24.08/3.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 24.08/3.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 24.08/3.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 24.08/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 24.08/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 24.08/3.49      | ~ v2_pre_topc(X1)
% 24.08/3.49      | ~ v2_pre_topc(X2)
% 24.08/3.49      | ~ l1_pre_topc(X1)
% 24.08/3.49      | ~ l1_pre_topc(X2)
% 24.08/3.49      | ~ v1_funct_1(X0) ),
% 24.08/3.49      inference(cnf_transformation,[],[f127]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_17491,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ v5_pre_topc(sK6,X0,sK4)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
% 24.08/3.49      | ~ v2_pre_topc(X0)
% 24.08/3.49      | ~ v2_pre_topc(sK4)
% 24.08/3.49      | ~ l1_pre_topc(X0)
% 24.08/3.49      | ~ l1_pre_topc(sK4)
% 24.08/3.49      | ~ v1_funct_1(sK6) ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_35]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_17503,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ v5_pre_topc(sK6,sK3,sK4)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 24.08/3.49      | ~ v2_pre_topc(sK4)
% 24.08/3.49      | ~ v2_pre_topc(sK3)
% 24.08/3.49      | ~ l1_pre_topc(sK4)
% 24.08/3.49      | ~ l1_pre_topc(sK3)
% 24.08/3.49      | ~ v1_funct_1(sK6) ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_17491]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_42276,plain,
% 24.08/3.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_8756,c_48,c_47,c_46,c_45,c_41,c_4101,c_4113,c_7412,
% 24.08/3.49                 c_8593,c_13023,c_17503]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_42277,plain,
% 24.08/3.49      ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 24.08/3.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_42276]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_42278,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_42277]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_50570,plain,
% 24.08/3.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_46600,c_42278]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_50571,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_50570]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_50578,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14378,c_50571]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_50577,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3845,c_50571]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_57768,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_xboole_0(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_7284,c_50577]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_57885,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_52530,c_133,c_15585,c_50578,c_51674,c_57768]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_57891,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | v1_funct_2(sK6,k1_relat_1(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14378,c_57885]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_61779,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_52553,c_51675,c_57891]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_61785,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0 | l1_pre_topc(sK4) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_7398,c_61779]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_62115,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0 ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_51621,c_52,c_61785]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_62127,plain,
% 24.08/3.49      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(demodulation,[status(thm)],[c_62115,c_57885]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_28,plain,
% 24.08/3.49      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 24.08/3.49      inference(cnf_transformation,[],[f96]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3837,plain,
% 24.08/3.49      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5731,plain,
% 24.08/3.49      ( k1_relat_1(sK2(X0,X1)) = X0
% 24.08/3.49      | v1_funct_2(sK2(X0,X1),X0,X1) != iProver_top
% 24.08/3.49      | v1_funct_1(sK2(X0,X1)) != iProver_top
% 24.08/3.49      | v1_relat_1(sK2(X0,X1)) != iProver_top
% 24.08/3.49      | v1_xboole_0(X1) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3837,c_3815]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_27,plain,
% 24.08/3.49      ( v1_relat_1(sK2(X0,X1)) ),
% 24.08/3.49      inference(cnf_transformation,[],[f97]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_85,plain,
% 24.08/3.49      ( v1_relat_1(sK2(X0,X1)) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_25,plain,
% 24.08/3.49      ( v1_funct_1(sK2(X0,X1)) ),
% 24.08/3.49      inference(cnf_transformation,[],[f99]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_91,plain,
% 24.08/3.49      ( v1_funct_1(sK2(X0,X1)) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_24,plain,
% 24.08/3.49      ( v1_funct_2(sK2(X0,X1),X0,X1) ),
% 24.08/3.49      inference(cnf_transformation,[],[f100]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_94,plain,
% 24.08/3.49      ( v1_funct_2(sK2(X0,X1),X0,X1) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_10580,plain,
% 24.08/3.49      ( k1_relat_1(sK2(X0,X1)) = X0 | v1_xboole_0(X1) = iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_5731,c_85,c_91,c_94]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_10591,plain,
% 24.08/3.49      ( k1_relat_1(sK2(X0,u1_struct_0(sK4))) = X0
% 24.08/3.49      | v1_xboole_0(sK6) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_10580,c_8212]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_20,plain,
% 24.08/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 24.08/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 24.08/3.49      | ~ v1_funct_1(X0)
% 24.08/3.49      | ~ v1_xboole_0(X0)
% 24.08/3.49      | v1_xboole_0(X1)
% 24.08/3.49      | v1_xboole_0(X2) ),
% 24.08/3.49      inference(cnf_transformation,[],[f92]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_14,plain,
% 24.08/3.49      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 24.08/3.49      inference(cnf_transformation,[],[f86]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_264,plain,
% 24.08/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 24.08/3.49      | ~ v1_funct_2(X0,X1,X2)
% 24.08/3.49      | ~ v1_xboole_0(X0)
% 24.08/3.49      | v1_xboole_0(X1)
% 24.08/3.49      | v1_xboole_0(X2) ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_20,c_14]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_265,plain,
% 24.08/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 24.08/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 24.08/3.49      | ~ v1_xboole_0(X0)
% 24.08/3.49      | v1_xboole_0(X1)
% 24.08/3.49      | v1_xboole_0(X2) ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_264]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3817,plain,
% 24.08/3.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 24.08/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 24.08/3.49      | v1_xboole_0(X0) != iProver_top
% 24.08/3.49      | v1_xboole_0(X1) = iProver_top
% 24.08/3.49      | v1_xboole_0(X2) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4962,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top
% 24.08/3.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top
% 24.08/3.49      | v1_xboole_0(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3827,c_3817]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5150,plain,
% 24.08/3.49      ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top
% 24.08/3.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top
% 24.08/3.49      | v1_xboole_0(sK6) != iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_4962,c_57]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5326,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
% 24.08/3.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top
% 24.08/3.49      | v1_xboole_0(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_5150,c_3846]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5606,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 24.08/3.49      | v1_xboole_0(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_5326,c_3846]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_10954,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 24.08/3.49      | k1_relat_1(sK2(X0,u1_struct_0(sK4))) = X0 ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_10591,c_5606]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_24558,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 24.08/3.49      | k1_relat_1(sK2(X0,u1_struct_0(sK4))) = X0
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_10954,c_3826]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5325,plain,
% 24.08/3.49      ( u1_struct_0(sK4) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | v1_relat_1(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_4708,c_3846]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_14340,plain,
% 24.08/3.49      ( u1_struct_0(sK4) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(sK3) = k1_relat_1(sK6) ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14330,c_5325]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_14821,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))) = iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14340,c_3962]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3831,plain,
% 24.08/3.49      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 24.08/3.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 24.08/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 24.08/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 24.08/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 24.08/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 24.08/3.49      | v2_pre_topc(X1) != iProver_top
% 24.08/3.49      | v2_pre_topc(X2) != iProver_top
% 24.08/3.49      | l1_pre_topc(X1) != iProver_top
% 24.08/3.49      | l1_pre_topc(X2) != iProver_top
% 24.08/3.49      | v1_funct_1(X0) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6466,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 24.08/3.49      | v2_pre_topc(sK4) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 24.08/3.49      | l1_pre_topc(sK4) != iProver_top
% 24.08/3.49      | v1_funct_1(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3827,c_3831]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_73,plain,
% 24.08/3.49      ( v2_pre_topc(X0) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 24.08/3.49      | l1_pre_topc(X0) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_75,plain,
% 24.08/3.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 24.08/3.49      | v2_pre_topc(sK3) != iProver_top
% 24.08/3.49      | l1_pre_topc(sK3) != iProver_top ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_73]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_76,plain,
% 24.08/3.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 24.08/3.49      | l1_pre_topc(X0) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_78,plain,
% 24.08/3.49      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
% 24.08/3.49      | l1_pre_topc(sK3) != iProver_top ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_76]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4212,plain,
% 24.08/3.49      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_29]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4213,plain,
% 24.08/3.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_4212]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4215,plain,
% 24.08/3.49      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_4213]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3830,plain,
% 24.08/3.49      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 24.08/3.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 24.08/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 24.08/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 24.08/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 24.08/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 24.08/3.49      | v2_pre_topc(X1) != iProver_top
% 24.08/3.49      | v2_pre_topc(X2) != iProver_top
% 24.08/3.49      | l1_pre_topc(X1) != iProver_top
% 24.08/3.49      | l1_pre_topc(X2) != iProver_top
% 24.08/3.49      | v1_funct_1(X0) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5724,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 24.08/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 24.08/3.49      | v2_pre_topc(sK4) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 24.08/3.49      | l1_pre_topc(sK4) != iProver_top
% 24.08/3.49      | v1_funct_1(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3827,c_3830]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4391,plain,
% 24.08/3.49      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 24.08/3.49      | ~ v2_pre_topc(sK4)
% 24.08/3.49      | ~ v2_pre_topc(sK3)
% 24.08/3.49      | ~ l1_pre_topc(sK4)
% 24.08/3.49      | ~ l1_pre_topc(sK3)
% 24.08/3.49      | ~ v1_funct_1(sK6) ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_32]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4392,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 24.08/3.49      | v2_pre_topc(sK4) != iProver_top
% 24.08/3.49      | v2_pre_topc(sK3) != iProver_top
% 24.08/3.49      | l1_pre_topc(sK4) != iProver_top
% 24.08/3.49      | l1_pre_topc(sK3) != iProver_top
% 24.08/3.49      | v1_funct_1(sK6) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_4391]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6064,plain,
% 24.08/3.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_5724,c_49,c_50,c_51,c_52,c_56,c_57,c_75,c_78,c_3878,
% 24.08/3.49                 c_3967,c_3887,c_4215,c_4392]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6065,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_6064]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6942,plain,
% 24.08/3.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_6466,c_49,c_50,c_51,c_52,c_56,c_57,c_75,c_78,c_3878,
% 24.08/3.49                 c_3967,c_3887,c_4215,c_4392,c_5724]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6943,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_6942]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_14809,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14340,c_6943]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_14822,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14340,c_3967]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_14825,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0))) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14340,c_3887]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_7,plain,
% 24.08/3.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 24.08/3.49      inference(cnf_transformation,[],[f121]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_14833,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 24.08/3.49      inference(demodulation,[status(thm)],[c_14825,c_7]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6949,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3962,c_6943]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_14808,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14340,c_6949]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_14918,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 24.08/3.49      inference(demodulation,[status(thm)],[c_14808,c_7]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_16875,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | u1_struct_0(sK3) = k1_relat_1(sK6) ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_14809,c_14822,c_14833,c_14918]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_16876,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_16875]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_16882,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14821,c_16876]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_17127,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14340,c_16882]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_27062,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | k1_relat_1(sK2(X0,u1_struct_0(sK4))) = X0
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_24558,c_17127]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4437,plain,
% 24.08/3.49      ( sK6 = sK6 ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_2846]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4616,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_2846]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5607,plain,
% 24.08/3.49      ( ~ v1_xboole_0(sK6)
% 24.08/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0 ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_5606]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5982,plain,
% 24.08/3.49      ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_6]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_2855,plain,
% 24.08/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 24.08/3.49      | v1_funct_2(X3,X4,X5)
% 24.08/3.49      | X3 != X0
% 24.08/3.49      | X4 != X1
% 24.08/3.49      | X5 != X2 ),
% 24.08/3.49      theory(equality) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4277,plain,
% 24.08/3.49      ( v1_funct_2(X0,X1,X2)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | X2 != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 24.08/3.49      | X0 != sK6 ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_2855]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4436,plain,
% 24.08/3.49      ( v1_funct_2(sK6,X0,X1)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 24.08/3.49      | sK6 != sK6 ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_4277]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5244,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 24.08/3.49      | sK6 != sK6 ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_4436]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6147,plain,
% 24.08/3.49      ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0)
% 24.08/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 24.08/3.49      | sK6 != sK6
% 24.08/3.49      | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_5244]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6149,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 24.08/3.49      | sK6 != sK6
% 24.08/3.49      | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_6147]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8386,plain,
% 24.08/3.49      ( ~ v1_relat_1(sK6)
% 24.08/3.49      | v1_xboole_0(sK6)
% 24.08/3.49      | u1_struct_0(sK3) = k1_relat_1(sK6) ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_8379]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_15598,plain,
% 24.08/3.49      ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ v1_xboole_0(k1_xboole_0)
% 24.08/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != k1_xboole_0 ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_7904]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_28396,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_27062,c_57,c_5,c_4437,c_4616,c_5607,c_5982,c_6149,
% 24.08/3.49                 c_7154,c_8386,c_10697,c_15598,c_17127]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_28397,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(sK3) = k1_relat_1(sK6)
% 24.08/3.49      | v5_pre_topc(sK6,sK3,sK4) = iProver_top ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_28396]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_62212,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
% 24.08/3.49      | v5_pre_topc(k1_xboole_0,sK3,sK4) = iProver_top ),
% 24.08/3.49      inference(demodulation,[status(thm)],[c_62115,c_28397]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8168,plain,
% 24.08/3.49      ( v1_funct_2(X0,X1,X2)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0)
% 24.08/3.49      | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 24.08/3.49      | X0 != sK6
% 24.08/3.49      | X2 != k1_xboole_0 ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_2855]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_11186,plain,
% 24.08/3.49      ( v1_funct_2(sK6,X0,X1)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0)
% 24.08/3.49      | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 24.08/3.49      | X1 != k1_xboole_0
% 24.08/3.49      | sK6 != sK6 ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_8168]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_12565,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0)
% 24.08/3.49      | X0 != k1_xboole_0
% 24.08/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 24.08/3.49      | sK6 != sK6 ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_11186]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_17533,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0)
% 24.08/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 24.08/3.49      | u1_struct_0(sK4) != k1_xboole_0
% 24.08/3.49      | sK6 != sK6 ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_12565]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_46607,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14378,c_6943]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8652,plain,
% 24.08/3.49      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
% 24.08/3.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 24.08/3.49      | ~ v2_pre_topc(sK4)
% 24.08/3.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 24.08/3.49      | ~ l1_pre_topc(sK4)
% 24.08/3.49      | ~ v1_funct_1(sK6) ),
% 24.08/3.49      inference(resolution,[status(thm)],[c_34,c_39]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6944,plain,
% 24.08/3.49      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_6943]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8842,plain,
% 24.08/3.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 24.08/3.49      | ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_8652,c_6944]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8843,plain,
% 24.08/3.49      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_8842]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6066,plain,
% 24.08/3.49      ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_6065]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_6950,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,sK3,sK4)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_6949]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_17492,plain,
% 24.08/3.49      ( ~ v5_pre_topc(sK6,X0,sK4)
% 24.08/3.49      | v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK4)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(sK4))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK4))))
% 24.08/3.49      | ~ v2_pre_topc(X0)
% 24.08/3.49      | ~ v2_pre_topc(sK4)
% 24.08/3.49      | ~ l1_pre_topc(X0)
% 24.08/3.49      | ~ l1_pre_topc(sK4)
% 24.08/3.49      | ~ v1_funct_1(sK6) ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_33]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_17499,plain,
% 24.08/3.49      ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
% 24.08/3.49      | ~ v5_pre_topc(sK6,sK3,sK4)
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 24.08/3.49      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 24.08/3.49      | ~ v2_pre_topc(sK4)
% 24.08/3.49      | ~ v2_pre_topc(sK3)
% 24.08/3.49      | ~ l1_pre_topc(sK4)
% 24.08/3.49      | ~ l1_pre_topc(sK3)
% 24.08/3.49      | ~ v1_funct_1(sK6) ),
% 24.08/3.49      inference(instantiation,[status(thm)],[c_17492]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_42030,plain,
% 24.08/3.49      ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
% 24.08/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_8843,c_48,c_47,c_46,c_45,c_41,c_4101,c_4113,c_6066,
% 24.08/3.49                 c_6950,c_17499]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_42032,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_42030]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_49069,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_46607,c_42032]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_49077,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14378,c_49069]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_49075,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3845,c_49069]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_56051,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | v1_xboole_0(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_7284,c_49075]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_56068,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK6),u1_pre_topc(sK3))),u1_struct_0(sK4)))) != iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_49077,c_133,c_15585,c_56051]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_56075,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK4)))) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_51595,c_56068]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_46618,plain,
% 24.08/3.49      ( sK6 = k1_xboole_0
% 24.08/3.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK4)))) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_14378,c_3887]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_56256,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_56075,c_133,c_15585,c_46618,c_56051]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_56258,plain,
% 24.08/3.49      ( ~ v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_56256]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_62266,plain,
% 24.08/3.49      ( u1_struct_0(sK4) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(sK3) = k1_relat_1(k1_xboole_0) ),
% 24.08/3.49      inference(demodulation,[status(thm)],[c_62115,c_14340]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_75806,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
% 24.08/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0 ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_62212,c_52,c_57,c_5,c_133,c_4437,c_4616,c_5607,c_5982,
% 24.08/3.49                 c_6149,c_15584,c_15585,c_15598,c_17534,c_46618,c_56051,
% 24.08/3.49                 c_56075,c_61785,c_62266]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_75807,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(sK3) = k1_relat_1(k1_xboole_0) ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_75806]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_62130,plain,
% 24.08/3.49      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) != iProver_top ),
% 24.08/3.49      inference(demodulation,[status(thm)],[c_62115,c_56256]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_97356,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0)
% 24.08/3.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK4)) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_75807,c_62130]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3847,plain,
% 24.08/3.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8,plain,
% 24.08/3.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 24.08/3.49      inference(cnf_transformation,[],[f122]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5729,plain,
% 24.08/3.49      ( m1_subset_1(sK2(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_8,c_3837]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8214,plain,
% 24.08/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 24.08/3.49      | v1_xboole_0(X1) != iProver_top
% 24.08/3.49      | v1_xboole_0(X0) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_8,c_3841]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_8353,plain,
% 24.08/3.49      ( v1_xboole_0(X0) != iProver_top
% 24.08/3.49      | v1_xboole_0(sK2(k1_xboole_0,X1)) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_5729,c_8214]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_10036,plain,
% 24.08/3.49      ( v1_xboole_0(sK2(k1_xboole_0,X0)) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3847,c_8353]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_10069,plain,
% 24.08/3.49      ( sK2(k1_xboole_0,X0) = k1_xboole_0 ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_10036,c_3846]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3840,plain,
% 24.08/3.49      ( v1_funct_2(sK2(X0,X1),X0,X1) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_10671,plain,
% 24.08/3.49      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_10069,c_3840]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_98958,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_relat_1(k1_xboole_0) ),
% 24.08/3.49      inference(forward_subsumption_resolution,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_97356,c_10671]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4963,plain,
% 24.08/3.49      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 24.08/3.49      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
% 24.08/3.49      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 24.08/3.49      | v1_xboole_0(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3887,c_3817]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5142,plain,
% 24.08/3.49      ( v1_xboole_0(u1_struct_0(sK4)) = iProver_top
% 24.08/3.49      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 24.08/3.49      | v1_xboole_0(sK6) != iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_4963,c_3878]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5324,plain,
% 24.08/3.49      ( u1_struct_0(sK4) = k1_xboole_0
% 24.08/3.49      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 24.08/3.49      | v1_xboole_0(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_5142,c_3846]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5483,plain,
% 24.08/3.49      ( u1_struct_0(sK4) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(sK3) = k1_xboole_0
% 24.08/3.49      | v1_xboole_0(sK6) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_5324,c_3846]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_10955,plain,
% 24.08/3.49      ( u1_struct_0(sK4) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(sK3) = k1_xboole_0
% 24.08/3.49      | k1_relat_1(sK2(X0,u1_struct_0(sK4))) = X0 ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_10591,c_5483]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_11872,plain,
% 24.08/3.49      ( u1_struct_0(sK4) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(sK3) = k1_xboole_0
% 24.08/3.49      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_10069,c_10955]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_62311,plain,
% 24.08/3.49      ( u1_struct_0(sK4) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(sK3) = k1_xboole_0
% 24.08/3.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 24.08/3.49      inference(demodulation,[status(thm)],[c_62115,c_5483]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_64201,plain,
% 24.08/3.49      ( ~ v1_xboole_0(k1_xboole_0)
% 24.08/3.49      | u1_struct_0(sK4) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(sK3) = k1_xboole_0 ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_62311]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_67933,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_xboole_0 | u1_struct_0(sK4) = k1_xboole_0 ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_11872,c_5,c_64201]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_67934,plain,
% 24.08/3.49      ( u1_struct_0(sK4) = k1_xboole_0 | u1_struct_0(sK3) = k1_xboole_0 ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_67933]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4656,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | v1_funct_1(sK6) != iProver_top
% 24.08/3.49      | v1_relat_1(sK6) != iProver_top
% 24.08/3.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_3827,c_3815]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_4831,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(sK6)
% 24.08/3.49      | v1_relat_1(sK6) != iProver_top
% 24.08/3.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_4656,c_56,c_57]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_62321,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0)
% 24.08/3.49      | v1_relat_1(k1_xboole_0) != iProver_top
% 24.08/3.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 24.08/3.49      inference(demodulation,[status(thm)],[c_62115,c_4831]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_3843,plain,
% 24.08/3.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5076,plain,
% 24.08/3.49      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_7,c_3843]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_71355,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0)
% 24.08/3.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_62321,c_5076]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_71362,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0)
% 24.08/3.49      | u1_struct_0(sK3) = k1_xboole_0
% 24.08/3.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK4)))) = iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_67934,c_71355]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_5078,plain,
% 24.08/3.49      ( v1_relat_1(k1_xboole_0) ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_5076]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_17534,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 24.08/3.49      | u1_struct_0(sK4) != k1_xboole_0
% 24.08/3.49      | sK6 != sK6
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) = iProver_top
% 24.08/3.49      | v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_xboole_0) != iProver_top ),
% 24.08/3.49      inference(predicate_to_equality,[status(thm)],[c_17533]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_64210,plain,
% 24.08/3.49      ( ~ v1_relat_1(k1_xboole_0)
% 24.08/3.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
% 24.08/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0) ),
% 24.08/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_62321]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_81699,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_xboole_0
% 24.08/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0) ),
% 24.08/3.49      inference(global_propositional_subsumption,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_71362,c_57,c_5,c_133,c_4437,c_4616,c_5078,c_5982,
% 24.08/3.49                 c_6149,c_15585,c_17534,c_46618,c_56051,c_56075,c_64201,
% 24.08/3.49                 c_64210]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_81700,plain,
% 24.08/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_relat_1(k1_xboole_0)
% 24.08/3.49      | u1_struct_0(sK3) = k1_xboole_0 ),
% 24.08/3.49      inference(renaming,[status(thm)],[c_81699]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_97354,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_xboole_0
% 24.08/3.49      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK4)) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_81700,c_62130]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_98959,plain,
% 24.08/3.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 24.08/3.49      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK4)) != iProver_top ),
% 24.08/3.49      inference(demodulation,[status(thm)],[c_98958,c_97354]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_62328,plain,
% 24.08/3.49      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 24.08/3.49      inference(demodulation,[status(thm)],[c_62115,c_3878]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_99049,plain,
% 24.08/3.49      ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK4)) = iProver_top ),
% 24.08/3.49      inference(demodulation,[status(thm)],[c_98958,c_62328]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_100396,plain,
% 24.08/3.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 24.08/3.49      inference(forward_subsumption_resolution,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_98959,c_99049]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_102113,plain,
% 24.08/3.49      ( u1_struct_0(sK3) = k1_xboole_0 ),
% 24.08/3.49      inference(demodulation,[status(thm)],[c_100396,c_98958]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_104627,plain,
% 24.08/3.49      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 24.08/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(light_normalisation,[status(thm)],[c_62127,c_102113]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_104630,plain,
% 24.08/3.49      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 24.08/3.49      inference(forward_subsumption_resolution,
% 24.08/3.49                [status(thm)],
% 24.08/3.49                [c_104627,c_10671]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(c_104632,plain,
% 24.08/3.49      ( l1_pre_topc(sK4) != iProver_top ),
% 24.08/3.49      inference(superposition,[status(thm)],[c_7398,c_104630]) ).
% 24.08/3.49  
% 24.08/3.49  cnf(contradiction,plain,
% 24.08/3.49      ( $false ),
% 24.08/3.49      inference(minisat,[status(thm)],[c_104632,c_52]) ).
% 24.08/3.49  
% 24.08/3.49  
% 24.08/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 24.08/3.49  
% 24.08/3.49  ------                               Statistics
% 24.08/3.49  
% 24.08/3.49  ------ Selected
% 24.08/3.49  
% 24.08/3.49  total_time:                             2.953
% 24.08/3.49  
%------------------------------------------------------------------------------
