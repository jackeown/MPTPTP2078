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
% DateTime   : Thu Dec  3 12:11:51 EST 2020

% Result     : Theorem 54.99s
% Output     : CNFRefutation 54.99s
% Verified   : 
% Statistics : Number of formulae       :  395 (22043 expanded)
%              Number of clauses        :  279 (4897 expanded)
%              Number of leaves         :   34 (6669 expanded)
%              Depth                    :   35
%              Number of atoms          : 1679 (259426 expanded)
%              Number of equality atoms :  741 (29953 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,conjecture,(
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

fof(f29,negated_conjecture,(
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
    inference(negated_conjecture,[],[f28])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f93,plain,(
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
    inference(nnf_transformation,[],[f63])).

fof(f94,plain,(
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
    inference(flattening,[],[f93])).

fof(f98,plain,(
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
     => ( ( ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK9 = X2
        & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
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
              | ~ v5_pre_topc(sK8,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK8,X0,X1) )
            & sK8 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
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
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
                  | ~ v5_pre_topc(X2,X0,sK7) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
                  | v5_pre_topc(X2,X0,sK7) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK7))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK7)
        & v2_pre_topc(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK6,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK6,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,
    ( ( ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
      | ~ v5_pre_topc(sK8,sK6,sK7) )
    & ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
      | v5_pre_topc(sK8,sK6,sK7) )
    & sK8 = sK9
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    & v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    & v1_funct_1(sK8)
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f94,f98,f97,f96,f95])).

fof(f167,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f99])).

fof(f171,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f99])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f80,plain,(
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
    inference(nnf_transformation,[],[f49])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f166,plain,(
    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f99])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f122,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f170,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) ),
    inference(cnf_transformation,[],[f99])).

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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f92,plain,(
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
    inference(nnf_transformation,[],[f61])).

fof(f159,plain,(
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
    inference(cnf_transformation,[],[f92])).

fof(f190,plain,(
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
    inference(equality_resolution,[],[f159])).

fof(f161,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f99])).

fof(f162,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f99])).

fof(f163,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f99])).

fof(f164,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f99])).

fof(f168,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f99])).

fof(f169,plain,(
    v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) ),
    inference(cnf_transformation,[],[f99])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f154,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f155,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f56,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f156,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f173,plain,
    ( ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f99])).

fof(f26,axiom,(
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

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f91,plain,(
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
    inference(nnf_transformation,[],[f59])).

fof(f158,plain,(
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
    inference(cnf_transformation,[],[f91])).

fof(f187,plain,(
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
    inference(equality_resolution,[],[f158])).

fof(f172,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f99])).

fof(f160,plain,(
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
    inference(cnf_transformation,[],[f92])).

fof(f189,plain,(
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
    inference(equality_resolution,[],[f160])).

fof(f157,plain,(
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
    inference(cnf_transformation,[],[f91])).

fof(f188,plain,(
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
    inference(equality_resolution,[],[f157])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f102,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f21,axiom,(
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

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f103,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f120,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f76])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f180,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f113])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f179,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f114])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f67,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f66])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f67,f68])).

fof(f101,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_67,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f167])).

cnf(c_5068,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_63,negated_conjecture,
    ( sK8 = sK9 ),
    inference(cnf_transformation,[],[f171])).

cnf(c_5128,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5068,c_63])).

cnf(c_39,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f134])).

cnf(c_5095,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_14982,plain,
    ( k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9) = u1_struct_0(sK6)
    | u1_struct_0(sK7) = k1_xboole_0
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5128,c_5095])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_5104,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8099,plain,
    ( k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9) = k1_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_5128,c_5104])).

cnf(c_14985,plain,
    ( u1_struct_0(sK7) = k1_xboole_0
    | u1_struct_0(sK6) = k1_relat_1(sK9)
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14982,c_8099])).

cnf(c_68,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f166])).

cnf(c_5067,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_5127,plain,
    ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5067,c_63])).

cnf(c_15125,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | u1_struct_0(sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14985,c_5127])).

cnf(c_15126,plain,
    ( u1_struct_0(sK7) = k1_xboole_0
    | u1_struct_0(sK6) = k1_relat_1(sK9) ),
    inference(renaming,[status(thm)],[c_15125])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_5110,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_64,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) ),
    inference(cnf_transformation,[],[f170])).

cnf(c_5071,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_60,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f190])).

cnf(c_5074,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_6105,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5071,c_5074])).

cnf(c_73,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f161])).

cnf(c_74,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_72,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f162])).

cnf(c_75,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_71,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f163])).

cnf(c_76,plain,
    ( v2_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_70,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f164])).

cnf(c_77,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_66,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f168])).

cnf(c_81,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_65,negated_conjecture,
    ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) ),
    inference(cnf_transformation,[],[f169])).

cnf(c_82,plain,
    ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_54,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f154])).

cnf(c_5324,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_5325,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5324])).

cnf(c_55,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f155])).

cnf(c_5664,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_5665,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5664])).

cnf(c_56,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_5810,plain,
    ( ~ l1_pre_topc(sK6)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_5811,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5810])).

cnf(c_6151,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6105,c_74,c_75,c_76,c_77,c_81,c_82,c_5325,c_5665,c_5811])).

cnf(c_6152,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6151])).

cnf(c_7036,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5110,c_6152])).

cnf(c_15199,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15126,c_7036])).

cnf(c_61,negated_conjecture,
    ( ~ v5_pre_topc(sK8,sK6,sK7)
    | ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
    inference(cnf_transformation,[],[f173])).

cnf(c_5073,plain,
    ( v5_pre_topc(sK8,sK6,sK7) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_5131,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5073,c_63])).

cnf(c_7043,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7036,c_5131])).

cnf(c_57,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f187])).

cnf(c_5895,plain,
    ( v5_pre_topc(X0,X1,sK7)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),sK7)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK7))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK7))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(sK7))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK7)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_8113,plain,
    ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | v5_pre_topc(X0,sK6,sK7)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK6)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_5895])).

cnf(c_8898,plain,
    ( ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | v5_pre_topc(sK9,sK6,sK7)
    | ~ v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK6)
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_8113])).

cnf(c_8899,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8898])).

cnf(c_59841,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(sK9,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_77716,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) ),
    inference(instantiation,[status(thm)],[c_59841])).

cnf(c_77717,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) = iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77716])).

cnf(c_139118,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15199,c_74,c_75,c_76,c_77,c_81,c_5127,c_5128,c_7043,c_8899,c_77717])).

cnf(c_62,negated_conjecture,
    ( v5_pre_topc(sK8,sK6,sK7)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_5072,plain,
    ( v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_5130,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5072,c_63])).

cnf(c_59,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f189])).

cnf(c_5075,plain,
    ( v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_6310,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5071,c_5075])).

cnf(c_6779,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6310,c_74,c_75,c_76,c_77,c_81,c_82,c_5325,c_5665,c_5811])).

cnf(c_6780,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6779])).

cnf(c_6783,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5130,c_6780])).

cnf(c_58,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f188])).

cnf(c_14056,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),X0)
    | ~ v5_pre_topc(sK9,sK6,X0)
    | ~ v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(X0))
    | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(X0))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(X0))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK6)
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_34373,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v5_pre_topc(sK9,sK6,sK7)
    | ~ v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK6)
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_14056])).

cnf(c_34374,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34373])).

cnf(c_139122,plain,
    ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_139118,c_74,c_75,c_76,c_77,c_81,c_5127,c_5128,c_6783,c_34374,c_77717])).

cnf(c_79,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_5136,plain,
    ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5127])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_7359,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK9)
    | sK9 = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7361,plain,
    ( ~ v1_xboole_0(sK9)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK9 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7359])).

cnf(c_8840,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK9)
    | X0 = sK9 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8842,plain,
    ( ~ v1_xboole_0(sK9)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_8840])).

cnf(c_3673,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_11071,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_3673])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_5106,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_11162,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_5071,c_5106])).

cnf(c_11170,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | v1_xboole_0(sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11162])).

cnf(c_12420,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3673])).

cnf(c_29,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_13300,plain,
    ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ v1_partfun1(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_13301,plain,
    ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) = iProver_top
    | v1_partfun1(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13300])).

cnf(c_41,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_5093,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_partfun1(X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_15536,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_partfun1(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5071,c_5093])).

cnf(c_15895,plain,
    ( v1_partfun1(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15536,c_81,c_82])).

cnf(c_15896,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
    | v1_partfun1(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_15895])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_5101,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_16072,plain,
    ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5128,c_5101])).

cnf(c_16082,plain,
    ( ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(u1_struct_0(sK7))
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ v1_xboole_0(sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16072])).

cnf(c_3674,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_9494,plain,
    ( X0 != X1
    | X0 = sK8
    | sK8 != X1 ),
    inference(instantiation,[status(thm)],[c_3674])).

cnf(c_39482,plain,
    ( X0 = sK8
    | X0 != sK9
    | sK8 != sK9 ),
    inference(instantiation,[status(thm)],[c_9494])).

cnf(c_39483,plain,
    ( sK8 != sK9
    | k1_xboole_0 = sK8
    | k1_xboole_0 != sK9 ),
    inference(instantiation,[status(thm)],[c_39482])).

cnf(c_3675,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_60070,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != X0 ),
    inference(instantiation,[status(thm)],[c_3675])).

cnf(c_60080,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_60070])).

cnf(c_3682,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_59378,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != X1
    | u1_struct_0(sK7) != X2
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_3682])).

cnf(c_62312,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK7))
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != X1
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_59378])).

cnf(c_62313,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != X0
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | sK9 != X1
    | v1_funct_2(X1,X0,u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62312])).

cnf(c_62315,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != k1_xboole_0
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | sK9 != k1_xboole_0
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_62313])).

cnf(c_64178,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_xboole_0(u1_struct_0(sK7))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_64436,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_64439,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_64436])).

cnf(c_64099,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | X2 != u1_struct_0(sK7)
    | X1 != u1_struct_0(sK6)
    | X0 != sK8 ),
    inference(instantiation,[status(thm)],[c_3682])).

cnf(c_70433,plain,
    ( v1_funct_2(X0,X1,u1_struct_0(sK7))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | X1 != u1_struct_0(sK6)
    | X0 != sK8
    | u1_struct_0(sK7) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_64099])).

cnf(c_70434,plain,
    ( X0 != u1_struct_0(sK6)
    | X1 != sK8
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | v1_funct_2(X1,X0,u1_struct_0(sK7)) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70433])).

cnf(c_70436,plain,
    ( u1_struct_0(sK7) != u1_struct_0(sK7)
    | k1_xboole_0 != u1_struct_0(sK6)
    | k1_xboole_0 != sK8
    | v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_70434])).

cnf(c_62298,plain,
    ( X0 != X1
    | u1_struct_0(sK7) != X1
    | u1_struct_0(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_3674])).

cnf(c_67171,plain,
    ( X0 != u1_struct_0(sK7)
    | u1_struct_0(sK7) = X0
    | u1_struct_0(sK7) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_62298])).

cnf(c_81780,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != u1_struct_0(sK7)
    | u1_struct_0(sK7) = u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | u1_struct_0(sK7) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_67171])).

cnf(c_82222,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(sK6))
    | X0 = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_82225,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_82222])).

cnf(c_16071,plain,
    ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5071,c_5101])).

cnf(c_16535,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16071,c_81,c_82])).

cnf(c_16523,plain,
    ( v1_xboole_0(u1_struct_0(sK7)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16072,c_81,c_5127])).

cnf(c_5119,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_16530,plain,
    ( u1_struct_0(sK7) = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_16523,c_5119])).

cnf(c_16730,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_16535,c_16530])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_5122,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_17323,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_16730,c_5122])).

cnf(c_16542,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_16535,c_5119])).

cnf(c_55798,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_17323,c_16542])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_189,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_20,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_195,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_208,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f180])).

cnf(c_209,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_233,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7360,plain,
    ( sK9 = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7359])).

cnf(c_7362,plain,
    ( sK9 = k1_xboole_0
    | v1_xboole_0(sK9) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7360])).

cnf(c_15537,plain,
    ( u1_struct_0(sK7) = k1_xboole_0
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v1_partfun1(sK9,u1_struct_0(sK6)) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5128,c_5093])).

cnf(c_15890,plain,
    ( v1_partfun1(sK9,u1_struct_0(sK6)) = iProver_top
    | u1_struct_0(sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15537,c_81,c_5127])).

cnf(c_15891,plain,
    ( u1_struct_0(sK7) = k1_xboole_0
    | v1_partfun1(sK9,u1_struct_0(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_15890])).

cnf(c_15892,plain,
    ( v1_partfun1(sK9,u1_struct_0(sK6))
    | u1_struct_0(sK7) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15891])).

cnf(c_16540,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_16535,c_5122])).

cnf(c_7348,plain,
    ( X0 != X1
    | sK9 != X1
    | sK9 = X0 ),
    inference(instantiation,[status(thm)],[c_3674])).

cnf(c_10612,plain,
    ( X0 != sK9
    | sK9 = X0
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_7348])).

cnf(c_26815,plain,
    ( sK8 != sK9
    | sK9 = sK8
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_10612])).

cnf(c_27406,plain,
    ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_partfun1(sK9,u1_struct_0(sK6))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_14981,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),sK9) = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5071,c_5095])).

cnf(c_8098,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),sK9) = k1_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_5071,c_5104])).

cnf(c_14986,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14981,c_8098])).

cnf(c_14992,plain,
    ( ~ v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14986])).

cnf(c_17387,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14986,c_65,c_14992])).

cnf(c_17388,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
    inference(renaming,[status(thm)],[c_17387])).

cnf(c_17445,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_17388,c_5071])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f179])).

cnf(c_17447,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17445,c_12])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_5103,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10195,plain,
    ( k7_relset_1(X0,k1_xboole_0,X1,X2) = k9_relat_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_5103])).

cnf(c_17726,plain,
    ( k7_relset_1(X0,k1_xboole_0,sK9,X1) = k9_relat_1(sK9,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_17447,c_10195])).

cnf(c_34567,plain,
    ( k7_relset_1(X0,k1_xboole_0,sK9,X1) = k9_relat_1(sK9,X1)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK9),u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17726,c_6152])).

cnf(c_5077,plain,
    ( v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_8087,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5071,c_5077])).

cnf(c_5339,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_5340,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5339])).

cnf(c_5686,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_5687,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5686])).

cnf(c_5842,plain,
    ( ~ l1_pre_topc(sK7)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v2_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_5843,plain,
    ( l1_pre_topc(sK7) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5842])).

cnf(c_8476,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8087,c_74,c_75,c_76,c_77,c_81,c_82,c_5340,c_5687,c_5843])).

cnf(c_8477,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8476])).

cnf(c_35948,plain,
    ( k7_relset_1(X0,k1_xboole_0,sK9,X1) = k9_relat_1(sK9,X1)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK9),u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_34567,c_8477])).

cnf(c_5076,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_7230,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5071,c_5076])).

cnf(c_7769,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7230,c_74,c_75,c_76,c_77,c_81,c_82,c_5340,c_5687,c_5843])).

cnf(c_7770,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7769])).

cnf(c_8482,plain,
    ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5130,c_8477])).

cnf(c_5896,plain,
    ( ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(X0,X1,sK7)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK7))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK7)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_8069,plain,
    ( ~ v5_pre_topc(X0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(X0,sK6,sK7)
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK6)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_5896])).

cnf(c_8888,plain,
    ( ~ v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK9,sK6,sK7)
    | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK6)
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_8069])).

cnf(c_8889,plain,
    ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8888])).

cnf(c_8973,plain,
    ( v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8482,c_74,c_75,c_76,c_77,c_81,c_5127,c_5128,c_5130,c_8477,c_8889])).

cnf(c_14085,plain,
    ( v5_pre_topc(sK9,X0,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v5_pre_topc(sK9,X0,sK7)
    | ~ v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK7)
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_34388,plain,
    ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v5_pre_topc(sK9,sK6,sK7)
    | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK6)
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_14085])).

cnf(c_34389,plain,
    ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34388])).

cnf(c_36552,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35948,c_74,c_75,c_76,c_77,c_81,c_5127,c_5128,c_5131,c_7770,c_8973,c_34389])).

cnf(c_36553,plain,
    ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_36552])).

cnf(c_36557,plain,
    ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5110,c_36553])).

cnf(c_36562,plain,
    ( ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_36557])).

cnf(c_3677,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9054,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK8,X2)
    | X2 != X1
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_3677])).

cnf(c_20792,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK8,k2_zfmisc_1(X2,X3))
    | k2_zfmisc_1(X2,X3) != X1
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_9054])).

cnf(c_44442,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(X0,X1))
    | ~ r1_tarski(sK9,X2)
    | k2_zfmisc_1(X0,X1) != X2
    | sK8 != sK9 ),
    inference(instantiation,[status(thm)],[c_20792])).

cnf(c_44444,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(sK9,k1_xboole_0)
    | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | sK8 != sK9 ),
    inference(instantiation,[status(thm)],[c_44442])).

cnf(c_50094,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK9,X2)
    | X2 != X1
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_3677])).

cnf(c_50096,plain,
    ( r1_tarski(sK9,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK9 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_50094])).

cnf(c_55800,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_xboole_0
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_17323,c_5122])).

cnf(c_59630,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_60034,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != X0 ),
    inference(instantiation,[status(thm)],[c_3675])).

cnf(c_60043,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60034])).

cnf(c_60045,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != k1_xboole_0
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_60043])).

cnf(c_64167,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != X0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7)
    | u1_struct_0(sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_3674])).

cnf(c_64169,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != k1_xboole_0
    | u1_struct_0(sK7) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_64167])).

cnf(c_59454,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK9,X2)
    | X2 != X1
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_3677])).

cnf(c_62354,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))
    | k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != X1
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_59454])).

cnf(c_67238,plain,
    ( ~ r1_tarski(sK8,X0)
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))
    | k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != X0
    | sK9 != sK8 ),
    inference(instantiation,[status(thm)],[c_62354])).

cnf(c_71324,plain,
    ( ~ r1_tarski(sK8,k2_zfmisc_1(X0,X1))
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))
    | k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != k2_zfmisc_1(X0,X1)
    | sK9 != sK8 ),
    inference(instantiation,[status(thm)],[c_67238])).

cnf(c_71326,plain,
    ( ~ r1_tarski(sK8,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))
    | k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | sK9 != sK8 ),
    inference(instantiation,[status(thm)],[c_71324])).

cnf(c_3678,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_93476,plain,
    ( k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = k2_zfmisc_1(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != X1
    | u1_struct_0(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_3678])).

cnf(c_93478,plain,
    ( k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != k1_xboole_0
    | u1_struct_0(sK6) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_93476])).

cnf(c_101751,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_55798,c_66,c_63,c_189,c_195,c_208,c_209,c_233,c_7362,c_11071,c_15892,c_16540,c_26815,c_27406,c_36562,c_44444,c_50096,c_55800,c_59630,c_60045,c_64169,c_71326,c_93478])).

cnf(c_101753,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_xboole_0(sK9)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_101751])).

cnf(c_60533,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK9,u1_struct_0(X3),u1_struct_0(X4))
    | u1_struct_0(X3) != X1
    | u1_struct_0(X4) != X2
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_3682])).

cnf(c_67594,plain,
    ( ~ v1_funct_2(sK9,X0,X1)
    | v1_funct_2(sK9,u1_struct_0(X2),u1_struct_0(X3))
    | u1_struct_0(X2) != X0
    | u1_struct_0(X3) != X1
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_60533])).

cnf(c_79332,plain,
    ( v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | u1_struct_0(X1) != u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | u1_struct_0(X0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_67594])).

cnf(c_81775,plain,
    ( v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7))
    | ~ v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | u1_struct_0(X0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | u1_struct_0(sK7) != u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_79332])).

cnf(c_107248,plain,
    ( ~ v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | u1_struct_0(sK7) != u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_81775])).

cnf(c_107249,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | u1_struct_0(sK7) != u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | sK9 != sK9
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_107248])).

cnf(c_108410,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(instantiation,[status(thm)],[c_3673])).

cnf(c_139126,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_139122,c_79,c_66,c_81,c_82,c_63,c_2,c_5136,c_7361,c_8842,c_11071,c_11170,c_12420,c_13301,c_15896,c_16082,c_39483,c_60080,c_62315,c_64178,c_64439,c_70436,c_77717,c_81780,c_82225,c_101753,c_107249,c_108410])).

cnf(c_0,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_5125,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10193,plain,
    ( k7_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),sK9,X0) = k9_relat_1(sK9,X0) ),
    inference(superposition,[status(thm)],[c_5071,c_5103])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_5105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_10973,plain,
    ( m1_subset_1(k9_relat_1(sK9,X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10193,c_5105])).

cnf(c_83,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_11442,plain,
    ( m1_subset_1(k9_relat_1(sK9,X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10973,c_83])).

cnf(c_23,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_5108,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12174,plain,
    ( m1_subset_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11442,c_5108])).

cnf(c_13416,plain,
    ( m1_subset_1(sK1(k9_relat_1(sK9,X0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top
    | v1_xboole_0(k9_relat_1(sK9,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5125,c_12174])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_5112,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14070,plain,
    ( r2_hidden(sK1(k9_relat_1(sK9,X0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top
    | v1_xboole_0(k9_relat_1(sK9,X0)) = iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13416,c_5112])).

cnf(c_17417,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | r2_hidden(sK1(k9_relat_1(sK9,X0)),k1_xboole_0) = iProver_top
    | v1_xboole_0(k9_relat_1(sK9,X0)) = iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_17388,c_14070])).

cnf(c_25037,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3673])).

cnf(c_36566,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17388,c_36557])).

cnf(c_36568,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | r1_tarski(sK9,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_36566,c_12])).

cnf(c_36558,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17388,c_36553])).

cnf(c_36560,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_36558,c_12])).

cnf(c_37418,plain,
    ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36568,c_17447,c_36560])).

cnf(c_37419,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_37418])).

cnf(c_5102,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15060,plain,
    ( v1_funct_2(X0,X1,k1_xboole_0) = iProver_top
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_5102])).

cnf(c_17730,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | v1_funct_2(sK9,X0,k1_xboole_0) = iProver_top
    | v1_partfun1(sK9,X0) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_17447,c_15060])).

cnf(c_54059,plain,
    ( v1_partfun1(sK9,X0) != iProver_top
    | v1_funct_2(sK9,X0,k1_xboole_0) = iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17730,c_81])).

cnf(c_54060,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | v1_funct_2(sK9,X0,k1_xboole_0) = iProver_top
    | v1_partfun1(sK9,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_54059])).

cnf(c_37422,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | v1_funct_2(sK9,u1_struct_0(sK6),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17388,c_37419])).

cnf(c_54066,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | v1_partfun1(sK9,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_54060,c_37422])).

cnf(c_59362,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != X2
    | u1_struct_0(sK6) != X1
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_3682])).

cnf(c_62288,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | sK9 != sK8 ),
    inference(instantiation,[status(thm)],[c_59362])).

cnf(c_62289,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | sK9 != sK8
    | v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62288])).

cnf(c_65459,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17417,c_79,c_81,c_65,c_63,c_5127,c_11071,c_14992,c_15537,c_25037,c_26815,c_37419,c_54066,c_62289,c_64169])).

cnf(c_139130,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(k1_relat_1(sK9),u1_struct_0(sK7))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_139126,c_65459])).

cnf(c_139133,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | r1_tarski(sK9,k2_zfmisc_1(k1_relat_1(sK9),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15126,c_139130])).

cnf(c_139134,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | r1_tarski(sK9,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_139133,c_12])).

cnf(c_5109,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6293,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5128,c_5109])).

cnf(c_15203,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15126,c_6293])).

cnf(c_15213,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | r1_tarski(sK9,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15203,c_12])).

cnf(c_139350,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_139134,c_15213])).

cnf(c_139575,plain,
    ( v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_139350,c_36557])).

cnf(c_5070,plain,
    ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_65551,plain,
    ( v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_65459,c_5070])).

cnf(c_6292,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5071,c_5109])).

cnf(c_65548,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_65459,c_6292])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_139575,c_65551,c_65548])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:28:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 54.99/7.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 54.99/7.51  
% 54.99/7.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 54.99/7.51  
% 54.99/7.51  ------  iProver source info
% 54.99/7.51  
% 54.99/7.51  git: date: 2020-06-30 10:37:57 +0100
% 54.99/7.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 54.99/7.51  git: non_committed_changes: false
% 54.99/7.51  git: last_make_outside_of_git: false
% 54.99/7.51  
% 54.99/7.51  ------ 
% 54.99/7.51  
% 54.99/7.51  ------ Input Options
% 54.99/7.51  
% 54.99/7.51  --out_options                           all
% 54.99/7.51  --tptp_safe_out                         true
% 54.99/7.51  --problem_path                          ""
% 54.99/7.51  --include_path                          ""
% 54.99/7.51  --clausifier                            res/vclausify_rel
% 54.99/7.51  --clausifier_options                    ""
% 54.99/7.51  --stdin                                 false
% 54.99/7.51  --stats_out                             all
% 54.99/7.51  
% 54.99/7.51  ------ General Options
% 54.99/7.51  
% 54.99/7.51  --fof                                   false
% 54.99/7.51  --time_out_real                         305.
% 54.99/7.51  --time_out_virtual                      -1.
% 54.99/7.51  --symbol_type_check                     false
% 54.99/7.51  --clausify_out                          false
% 54.99/7.51  --sig_cnt_out                           false
% 54.99/7.51  --trig_cnt_out                          false
% 54.99/7.51  --trig_cnt_out_tolerance                1.
% 54.99/7.51  --trig_cnt_out_sk_spl                   false
% 54.99/7.51  --abstr_cl_out                          false
% 54.99/7.51  
% 54.99/7.51  ------ Global Options
% 54.99/7.51  
% 54.99/7.51  --schedule                              default
% 54.99/7.51  --add_important_lit                     false
% 54.99/7.51  --prop_solver_per_cl                    1000
% 54.99/7.51  --min_unsat_core                        false
% 54.99/7.51  --soft_assumptions                      false
% 54.99/7.51  --soft_lemma_size                       3
% 54.99/7.51  --prop_impl_unit_size                   0
% 54.99/7.51  --prop_impl_unit                        []
% 54.99/7.51  --share_sel_clauses                     true
% 54.99/7.51  --reset_solvers                         false
% 54.99/7.51  --bc_imp_inh                            [conj_cone]
% 54.99/7.51  --conj_cone_tolerance                   3.
% 54.99/7.51  --extra_neg_conj                        none
% 54.99/7.51  --large_theory_mode                     true
% 54.99/7.51  --prolific_symb_bound                   200
% 54.99/7.51  --lt_threshold                          2000
% 54.99/7.51  --clause_weak_htbl                      true
% 54.99/7.51  --gc_record_bc_elim                     false
% 54.99/7.51  
% 54.99/7.51  ------ Preprocessing Options
% 54.99/7.51  
% 54.99/7.51  --preprocessing_flag                    true
% 54.99/7.51  --time_out_prep_mult                    0.1
% 54.99/7.51  --splitting_mode                        input
% 54.99/7.51  --splitting_grd                         true
% 54.99/7.51  --splitting_cvd                         false
% 54.99/7.51  --splitting_cvd_svl                     false
% 54.99/7.51  --splitting_nvd                         32
% 54.99/7.51  --sub_typing                            true
% 54.99/7.51  --prep_gs_sim                           true
% 54.99/7.51  --prep_unflatten                        true
% 54.99/7.51  --prep_res_sim                          true
% 54.99/7.51  --prep_upred                            true
% 54.99/7.51  --prep_sem_filter                       exhaustive
% 54.99/7.51  --prep_sem_filter_out                   false
% 54.99/7.51  --pred_elim                             true
% 54.99/7.51  --res_sim_input                         true
% 54.99/7.51  --eq_ax_congr_red                       true
% 54.99/7.51  --pure_diseq_elim                       true
% 54.99/7.51  --brand_transform                       false
% 54.99/7.51  --non_eq_to_eq                          false
% 54.99/7.51  --prep_def_merge                        true
% 54.99/7.51  --prep_def_merge_prop_impl              false
% 54.99/7.51  --prep_def_merge_mbd                    true
% 54.99/7.51  --prep_def_merge_tr_red                 false
% 54.99/7.51  --prep_def_merge_tr_cl                  false
% 54.99/7.51  --smt_preprocessing                     true
% 54.99/7.51  --smt_ac_axioms                         fast
% 54.99/7.51  --preprocessed_out                      false
% 54.99/7.51  --preprocessed_stats                    false
% 54.99/7.51  
% 54.99/7.51  ------ Abstraction refinement Options
% 54.99/7.51  
% 54.99/7.51  --abstr_ref                             []
% 54.99/7.51  --abstr_ref_prep                        false
% 54.99/7.51  --abstr_ref_until_sat                   false
% 54.99/7.51  --abstr_ref_sig_restrict                funpre
% 54.99/7.51  --abstr_ref_af_restrict_to_split_sk     false
% 54.99/7.51  --abstr_ref_under                       []
% 54.99/7.51  
% 54.99/7.51  ------ SAT Options
% 54.99/7.51  
% 54.99/7.51  --sat_mode                              false
% 54.99/7.51  --sat_fm_restart_options                ""
% 54.99/7.51  --sat_gr_def                            false
% 54.99/7.51  --sat_epr_types                         true
% 54.99/7.51  --sat_non_cyclic_types                  false
% 54.99/7.51  --sat_finite_models                     false
% 54.99/7.51  --sat_fm_lemmas                         false
% 54.99/7.51  --sat_fm_prep                           false
% 54.99/7.51  --sat_fm_uc_incr                        true
% 54.99/7.51  --sat_out_model                         small
% 54.99/7.51  --sat_out_clauses                       false
% 54.99/7.51  
% 54.99/7.51  ------ QBF Options
% 54.99/7.51  
% 54.99/7.51  --qbf_mode                              false
% 54.99/7.51  --qbf_elim_univ                         false
% 54.99/7.51  --qbf_dom_inst                          none
% 54.99/7.51  --qbf_dom_pre_inst                      false
% 54.99/7.51  --qbf_sk_in                             false
% 54.99/7.51  --qbf_pred_elim                         true
% 54.99/7.51  --qbf_split                             512
% 54.99/7.51  
% 54.99/7.51  ------ BMC1 Options
% 54.99/7.51  
% 54.99/7.51  --bmc1_incremental                      false
% 54.99/7.51  --bmc1_axioms                           reachable_all
% 54.99/7.51  --bmc1_min_bound                        0
% 54.99/7.51  --bmc1_max_bound                        -1
% 54.99/7.51  --bmc1_max_bound_default                -1
% 54.99/7.51  --bmc1_symbol_reachability              true
% 54.99/7.51  --bmc1_property_lemmas                  false
% 54.99/7.51  --bmc1_k_induction                      false
% 54.99/7.51  --bmc1_non_equiv_states                 false
% 54.99/7.51  --bmc1_deadlock                         false
% 54.99/7.51  --bmc1_ucm                              false
% 54.99/7.51  --bmc1_add_unsat_core                   none
% 54.99/7.51  --bmc1_unsat_core_children              false
% 54.99/7.51  --bmc1_unsat_core_extrapolate_axioms    false
% 54.99/7.51  --bmc1_out_stat                         full
% 54.99/7.51  --bmc1_ground_init                      false
% 54.99/7.51  --bmc1_pre_inst_next_state              false
% 54.99/7.51  --bmc1_pre_inst_state                   false
% 54.99/7.51  --bmc1_pre_inst_reach_state             false
% 54.99/7.51  --bmc1_out_unsat_core                   false
% 54.99/7.51  --bmc1_aig_witness_out                  false
% 54.99/7.51  --bmc1_verbose                          false
% 54.99/7.51  --bmc1_dump_clauses_tptp                false
% 54.99/7.51  --bmc1_dump_unsat_core_tptp             false
% 54.99/7.51  --bmc1_dump_file                        -
% 54.99/7.51  --bmc1_ucm_expand_uc_limit              128
% 54.99/7.51  --bmc1_ucm_n_expand_iterations          6
% 54.99/7.51  --bmc1_ucm_extend_mode                  1
% 54.99/7.51  --bmc1_ucm_init_mode                    2
% 54.99/7.51  --bmc1_ucm_cone_mode                    none
% 54.99/7.51  --bmc1_ucm_reduced_relation_type        0
% 54.99/7.51  --bmc1_ucm_relax_model                  4
% 54.99/7.51  --bmc1_ucm_full_tr_after_sat            true
% 54.99/7.51  --bmc1_ucm_expand_neg_assumptions       false
% 54.99/7.51  --bmc1_ucm_layered_model                none
% 54.99/7.51  --bmc1_ucm_max_lemma_size               10
% 54.99/7.51  
% 54.99/7.51  ------ AIG Options
% 54.99/7.51  
% 54.99/7.51  --aig_mode                              false
% 54.99/7.51  
% 54.99/7.51  ------ Instantiation Options
% 54.99/7.51  
% 54.99/7.51  --instantiation_flag                    true
% 54.99/7.51  --inst_sos_flag                         true
% 54.99/7.51  --inst_sos_phase                        true
% 54.99/7.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 54.99/7.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 54.99/7.51  --inst_lit_sel_side                     num_symb
% 54.99/7.51  --inst_solver_per_active                1400
% 54.99/7.51  --inst_solver_calls_frac                1.
% 54.99/7.51  --inst_passive_queue_type               priority_queues
% 54.99/7.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 54.99/7.51  --inst_passive_queues_freq              [25;2]
% 54.99/7.51  --inst_dismatching                      true
% 54.99/7.51  --inst_eager_unprocessed_to_passive     true
% 54.99/7.51  --inst_prop_sim_given                   true
% 54.99/7.51  --inst_prop_sim_new                     false
% 54.99/7.51  --inst_subs_new                         false
% 54.99/7.51  --inst_eq_res_simp                      false
% 54.99/7.51  --inst_subs_given                       false
% 54.99/7.51  --inst_orphan_elimination               true
% 54.99/7.51  --inst_learning_loop_flag               true
% 54.99/7.51  --inst_learning_start                   3000
% 54.99/7.51  --inst_learning_factor                  2
% 54.99/7.51  --inst_start_prop_sim_after_learn       3
% 54.99/7.51  --inst_sel_renew                        solver
% 54.99/7.51  --inst_lit_activity_flag                true
% 54.99/7.51  --inst_restr_to_given                   false
% 54.99/7.51  --inst_activity_threshold               500
% 54.99/7.51  --inst_out_proof                        true
% 54.99/7.51  
% 54.99/7.51  ------ Resolution Options
% 54.99/7.51  
% 54.99/7.51  --resolution_flag                       true
% 54.99/7.51  --res_lit_sel                           adaptive
% 54.99/7.51  --res_lit_sel_side                      none
% 54.99/7.51  --res_ordering                          kbo
% 54.99/7.51  --res_to_prop_solver                    active
% 54.99/7.51  --res_prop_simpl_new                    false
% 54.99/7.51  --res_prop_simpl_given                  true
% 54.99/7.51  --res_passive_queue_type                priority_queues
% 54.99/7.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 54.99/7.51  --res_passive_queues_freq               [15;5]
% 54.99/7.51  --res_forward_subs                      full
% 54.99/7.51  --res_backward_subs                     full
% 54.99/7.51  --res_forward_subs_resolution           true
% 54.99/7.51  --res_backward_subs_resolution          true
% 54.99/7.51  --res_orphan_elimination                true
% 54.99/7.51  --res_time_limit                        2.
% 54.99/7.51  --res_out_proof                         true
% 54.99/7.51  
% 54.99/7.51  ------ Superposition Options
% 54.99/7.51  
% 54.99/7.51  --superposition_flag                    true
% 54.99/7.51  --sup_passive_queue_type                priority_queues
% 54.99/7.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 54.99/7.51  --sup_passive_queues_freq               [8;1;4]
% 54.99/7.51  --demod_completeness_check              fast
% 54.99/7.51  --demod_use_ground                      true
% 54.99/7.51  --sup_to_prop_solver                    passive
% 54.99/7.51  --sup_prop_simpl_new                    true
% 54.99/7.51  --sup_prop_simpl_given                  true
% 54.99/7.51  --sup_fun_splitting                     true
% 54.99/7.51  --sup_smt_interval                      50000
% 54.99/7.51  
% 54.99/7.51  ------ Superposition Simplification Setup
% 54.99/7.51  
% 54.99/7.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 54.99/7.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 54.99/7.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 54.99/7.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 54.99/7.51  --sup_full_triv                         [TrivRules;PropSubs]
% 54.99/7.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 54.99/7.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 54.99/7.51  --sup_immed_triv                        [TrivRules]
% 54.99/7.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 54.99/7.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 54.99/7.51  --sup_immed_bw_main                     []
% 54.99/7.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 54.99/7.51  --sup_input_triv                        [Unflattening;TrivRules]
% 54.99/7.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 54.99/7.51  --sup_input_bw                          []
% 54.99/7.51  
% 54.99/7.51  ------ Combination Options
% 54.99/7.51  
% 54.99/7.51  --comb_res_mult                         3
% 54.99/7.51  --comb_sup_mult                         2
% 54.99/7.51  --comb_inst_mult                        10
% 54.99/7.51  
% 54.99/7.51  ------ Debug Options
% 54.99/7.51  
% 54.99/7.51  --dbg_backtrace                         false
% 54.99/7.51  --dbg_dump_prop_clauses                 false
% 54.99/7.51  --dbg_dump_prop_clauses_file            -
% 54.99/7.51  --dbg_out_stat                          false
% 54.99/7.51  ------ Parsing...
% 54.99/7.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 54.99/7.51  
% 54.99/7.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 54.99/7.51  
% 54.99/7.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 54.99/7.51  
% 54.99/7.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 54.99/7.51  ------ Proving...
% 54.99/7.51  ------ Problem Properties 
% 54.99/7.51  
% 54.99/7.51  
% 54.99/7.51  clauses                                 70
% 54.99/7.51  conjectures                             13
% 54.99/7.51  EPR                                     19
% 54.99/7.51  Horn                                    53
% 54.99/7.51  unary                                   17
% 54.99/7.51  binary                                  19
% 54.99/7.51  lits                                    210
% 54.99/7.51  lits eq                                 26
% 54.99/7.51  fd_pure                                 0
% 54.99/7.51  fd_pseudo                               0
% 54.99/7.51  fd_cond                                 6
% 54.99/7.51  fd_pseudo_cond                          4
% 54.99/7.51  AC symbols                              0
% 54.99/7.51  
% 54.99/7.51  ------ Schedule dynamic 5 is on 
% 54.99/7.51  
% 54.99/7.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 54.99/7.51  
% 54.99/7.51  
% 54.99/7.51  ------ 
% 54.99/7.51  Current options:
% 54.99/7.51  ------ 
% 54.99/7.51  
% 54.99/7.51  ------ Input Options
% 54.99/7.51  
% 54.99/7.51  --out_options                           all
% 54.99/7.51  --tptp_safe_out                         true
% 54.99/7.51  --problem_path                          ""
% 54.99/7.51  --include_path                          ""
% 54.99/7.51  --clausifier                            res/vclausify_rel
% 54.99/7.51  --clausifier_options                    ""
% 54.99/7.51  --stdin                                 false
% 54.99/7.51  --stats_out                             all
% 54.99/7.51  
% 54.99/7.51  ------ General Options
% 54.99/7.51  
% 54.99/7.51  --fof                                   false
% 54.99/7.51  --time_out_real                         305.
% 54.99/7.51  --time_out_virtual                      -1.
% 54.99/7.51  --symbol_type_check                     false
% 54.99/7.51  --clausify_out                          false
% 54.99/7.51  --sig_cnt_out                           false
% 54.99/7.51  --trig_cnt_out                          false
% 54.99/7.51  --trig_cnt_out_tolerance                1.
% 54.99/7.51  --trig_cnt_out_sk_spl                   false
% 54.99/7.51  --abstr_cl_out                          false
% 54.99/7.51  
% 54.99/7.51  ------ Global Options
% 54.99/7.51  
% 54.99/7.51  --schedule                              default
% 54.99/7.51  --add_important_lit                     false
% 54.99/7.51  --prop_solver_per_cl                    1000
% 54.99/7.51  --min_unsat_core                        false
% 54.99/7.51  --soft_assumptions                      false
% 54.99/7.51  --soft_lemma_size                       3
% 54.99/7.51  --prop_impl_unit_size                   0
% 54.99/7.51  --prop_impl_unit                        []
% 54.99/7.51  --share_sel_clauses                     true
% 54.99/7.51  --reset_solvers                         false
% 54.99/7.51  --bc_imp_inh                            [conj_cone]
% 54.99/7.51  --conj_cone_tolerance                   3.
% 54.99/7.51  --extra_neg_conj                        none
% 54.99/7.51  --large_theory_mode                     true
% 54.99/7.51  --prolific_symb_bound                   200
% 54.99/7.51  --lt_threshold                          2000
% 54.99/7.51  --clause_weak_htbl                      true
% 54.99/7.51  --gc_record_bc_elim                     false
% 54.99/7.51  
% 54.99/7.51  ------ Preprocessing Options
% 54.99/7.51  
% 54.99/7.51  --preprocessing_flag                    true
% 54.99/7.51  --time_out_prep_mult                    0.1
% 54.99/7.51  --splitting_mode                        input
% 54.99/7.51  --splitting_grd                         true
% 54.99/7.51  --splitting_cvd                         false
% 54.99/7.51  --splitting_cvd_svl                     false
% 54.99/7.51  --splitting_nvd                         32
% 54.99/7.51  --sub_typing                            true
% 54.99/7.51  --prep_gs_sim                           true
% 54.99/7.51  --prep_unflatten                        true
% 54.99/7.51  --prep_res_sim                          true
% 54.99/7.51  --prep_upred                            true
% 54.99/7.51  --prep_sem_filter                       exhaustive
% 54.99/7.51  --prep_sem_filter_out                   false
% 54.99/7.51  --pred_elim                             true
% 54.99/7.51  --res_sim_input                         true
% 54.99/7.51  --eq_ax_congr_red                       true
% 54.99/7.51  --pure_diseq_elim                       true
% 54.99/7.51  --brand_transform                       false
% 54.99/7.51  --non_eq_to_eq                          false
% 54.99/7.51  --prep_def_merge                        true
% 54.99/7.51  --prep_def_merge_prop_impl              false
% 54.99/7.51  --prep_def_merge_mbd                    true
% 54.99/7.51  --prep_def_merge_tr_red                 false
% 54.99/7.51  --prep_def_merge_tr_cl                  false
% 54.99/7.51  --smt_preprocessing                     true
% 54.99/7.51  --smt_ac_axioms                         fast
% 54.99/7.51  --preprocessed_out                      false
% 54.99/7.51  --preprocessed_stats                    false
% 54.99/7.51  
% 54.99/7.51  ------ Abstraction refinement Options
% 54.99/7.51  
% 54.99/7.51  --abstr_ref                             []
% 54.99/7.51  --abstr_ref_prep                        false
% 54.99/7.51  --abstr_ref_until_sat                   false
% 54.99/7.51  --abstr_ref_sig_restrict                funpre
% 54.99/7.51  --abstr_ref_af_restrict_to_split_sk     false
% 54.99/7.51  --abstr_ref_under                       []
% 54.99/7.51  
% 54.99/7.51  ------ SAT Options
% 54.99/7.51  
% 54.99/7.51  --sat_mode                              false
% 54.99/7.51  --sat_fm_restart_options                ""
% 54.99/7.51  --sat_gr_def                            false
% 54.99/7.51  --sat_epr_types                         true
% 54.99/7.51  --sat_non_cyclic_types                  false
% 54.99/7.51  --sat_finite_models                     false
% 54.99/7.51  --sat_fm_lemmas                         false
% 54.99/7.51  --sat_fm_prep                           false
% 54.99/7.51  --sat_fm_uc_incr                        true
% 54.99/7.51  --sat_out_model                         small
% 54.99/7.51  --sat_out_clauses                       false
% 54.99/7.51  
% 54.99/7.51  ------ QBF Options
% 54.99/7.51  
% 54.99/7.51  --qbf_mode                              false
% 54.99/7.51  --qbf_elim_univ                         false
% 54.99/7.51  --qbf_dom_inst                          none
% 54.99/7.51  --qbf_dom_pre_inst                      false
% 54.99/7.51  --qbf_sk_in                             false
% 54.99/7.51  --qbf_pred_elim                         true
% 54.99/7.51  --qbf_split                             512
% 54.99/7.51  
% 54.99/7.51  ------ BMC1 Options
% 54.99/7.51  
% 54.99/7.51  --bmc1_incremental                      false
% 54.99/7.51  --bmc1_axioms                           reachable_all
% 54.99/7.51  --bmc1_min_bound                        0
% 54.99/7.51  --bmc1_max_bound                        -1
% 54.99/7.51  --bmc1_max_bound_default                -1
% 54.99/7.51  --bmc1_symbol_reachability              true
% 54.99/7.51  --bmc1_property_lemmas                  false
% 54.99/7.51  --bmc1_k_induction                      false
% 54.99/7.51  --bmc1_non_equiv_states                 false
% 54.99/7.51  --bmc1_deadlock                         false
% 54.99/7.51  --bmc1_ucm                              false
% 54.99/7.51  --bmc1_add_unsat_core                   none
% 54.99/7.51  --bmc1_unsat_core_children              false
% 54.99/7.51  --bmc1_unsat_core_extrapolate_axioms    false
% 54.99/7.51  --bmc1_out_stat                         full
% 54.99/7.51  --bmc1_ground_init                      false
% 54.99/7.51  --bmc1_pre_inst_next_state              false
% 54.99/7.51  --bmc1_pre_inst_state                   false
% 54.99/7.51  --bmc1_pre_inst_reach_state             false
% 54.99/7.51  --bmc1_out_unsat_core                   false
% 54.99/7.51  --bmc1_aig_witness_out                  false
% 54.99/7.51  --bmc1_verbose                          false
% 54.99/7.51  --bmc1_dump_clauses_tptp                false
% 54.99/7.51  --bmc1_dump_unsat_core_tptp             false
% 54.99/7.51  --bmc1_dump_file                        -
% 54.99/7.51  --bmc1_ucm_expand_uc_limit              128
% 54.99/7.51  --bmc1_ucm_n_expand_iterations          6
% 54.99/7.51  --bmc1_ucm_extend_mode                  1
% 54.99/7.51  --bmc1_ucm_init_mode                    2
% 54.99/7.51  --bmc1_ucm_cone_mode                    none
% 54.99/7.51  --bmc1_ucm_reduced_relation_type        0
% 54.99/7.51  --bmc1_ucm_relax_model                  4
% 54.99/7.51  --bmc1_ucm_full_tr_after_sat            true
% 54.99/7.51  --bmc1_ucm_expand_neg_assumptions       false
% 54.99/7.51  --bmc1_ucm_layered_model                none
% 54.99/7.51  --bmc1_ucm_max_lemma_size               10
% 54.99/7.51  
% 54.99/7.51  ------ AIG Options
% 54.99/7.51  
% 54.99/7.51  --aig_mode                              false
% 54.99/7.51  
% 54.99/7.51  ------ Instantiation Options
% 54.99/7.51  
% 54.99/7.51  --instantiation_flag                    true
% 54.99/7.51  --inst_sos_flag                         true
% 54.99/7.51  --inst_sos_phase                        true
% 54.99/7.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 54.99/7.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 54.99/7.51  --inst_lit_sel_side                     none
% 54.99/7.51  --inst_solver_per_active                1400
% 54.99/7.51  --inst_solver_calls_frac                1.
% 54.99/7.51  --inst_passive_queue_type               priority_queues
% 54.99/7.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 54.99/7.51  --inst_passive_queues_freq              [25;2]
% 54.99/7.51  --inst_dismatching                      true
% 54.99/7.51  --inst_eager_unprocessed_to_passive     true
% 54.99/7.51  --inst_prop_sim_given                   true
% 54.99/7.51  --inst_prop_sim_new                     false
% 54.99/7.51  --inst_subs_new                         false
% 54.99/7.51  --inst_eq_res_simp                      false
% 54.99/7.51  --inst_subs_given                       false
% 54.99/7.51  --inst_orphan_elimination               true
% 54.99/7.51  --inst_learning_loop_flag               true
% 54.99/7.51  --inst_learning_start                   3000
% 54.99/7.51  --inst_learning_factor                  2
% 54.99/7.51  --inst_start_prop_sim_after_learn       3
% 54.99/7.51  --inst_sel_renew                        solver
% 54.99/7.51  --inst_lit_activity_flag                true
% 54.99/7.51  --inst_restr_to_given                   false
% 54.99/7.51  --inst_activity_threshold               500
% 54.99/7.51  --inst_out_proof                        true
% 54.99/7.51  
% 54.99/7.51  ------ Resolution Options
% 54.99/7.51  
% 54.99/7.51  --resolution_flag                       false
% 54.99/7.51  --res_lit_sel                           adaptive
% 54.99/7.51  --res_lit_sel_side                      none
% 54.99/7.51  --res_ordering                          kbo
% 54.99/7.51  --res_to_prop_solver                    active
% 54.99/7.51  --res_prop_simpl_new                    false
% 54.99/7.51  --res_prop_simpl_given                  true
% 54.99/7.51  --res_passive_queue_type                priority_queues
% 54.99/7.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 54.99/7.51  --res_passive_queues_freq               [15;5]
% 54.99/7.51  --res_forward_subs                      full
% 54.99/7.51  --res_backward_subs                     full
% 54.99/7.51  --res_forward_subs_resolution           true
% 54.99/7.51  --res_backward_subs_resolution          true
% 54.99/7.51  --res_orphan_elimination                true
% 54.99/7.51  --res_time_limit                        2.
% 54.99/7.51  --res_out_proof                         true
% 54.99/7.51  
% 54.99/7.51  ------ Superposition Options
% 54.99/7.51  
% 54.99/7.51  --superposition_flag                    true
% 54.99/7.51  --sup_passive_queue_type                priority_queues
% 54.99/7.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 54.99/7.51  --sup_passive_queues_freq               [8;1;4]
% 54.99/7.51  --demod_completeness_check              fast
% 54.99/7.51  --demod_use_ground                      true
% 54.99/7.51  --sup_to_prop_solver                    passive
% 54.99/7.51  --sup_prop_simpl_new                    true
% 54.99/7.51  --sup_prop_simpl_given                  true
% 54.99/7.51  --sup_fun_splitting                     true
% 54.99/7.51  --sup_smt_interval                      50000
% 54.99/7.51  
% 54.99/7.51  ------ Superposition Simplification Setup
% 54.99/7.51  
% 54.99/7.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 54.99/7.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 54.99/7.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 54.99/7.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 54.99/7.51  --sup_full_triv                         [TrivRules;PropSubs]
% 54.99/7.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 54.99/7.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 54.99/7.51  --sup_immed_triv                        [TrivRules]
% 54.99/7.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 54.99/7.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 54.99/7.51  --sup_immed_bw_main                     []
% 54.99/7.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 54.99/7.51  --sup_input_triv                        [Unflattening;TrivRules]
% 54.99/7.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 54.99/7.51  --sup_input_bw                          []
% 54.99/7.51  
% 54.99/7.51  ------ Combination Options
% 54.99/7.51  
% 54.99/7.51  --comb_res_mult                         3
% 54.99/7.51  --comb_sup_mult                         2
% 54.99/7.51  --comb_inst_mult                        10
% 54.99/7.51  
% 54.99/7.51  ------ Debug Options
% 54.99/7.51  
% 54.99/7.51  --dbg_backtrace                         false
% 54.99/7.51  --dbg_dump_prop_clauses                 false
% 54.99/7.51  --dbg_dump_prop_clauses_file            -
% 54.99/7.51  --dbg_out_stat                          false
% 54.99/7.51  
% 54.99/7.51  
% 54.99/7.51  
% 54.99/7.51  
% 54.99/7.51  ------ Proving...
% 54.99/7.51  
% 54.99/7.51  
% 54.99/7.51  % SZS status Theorem for theBenchmark.p
% 54.99/7.51  
% 54.99/7.51  % SZS output start CNFRefutation for theBenchmark.p
% 54.99/7.51  
% 54.99/7.51  fof(f28,conjecture,(
% 54.99/7.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f29,negated_conjecture,(
% 54.99/7.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 54.99/7.51    inference(negated_conjecture,[],[f28])).
% 54.99/7.51  
% 54.99/7.51  fof(f62,plain,(
% 54.99/7.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 54.99/7.51    inference(ennf_transformation,[],[f29])).
% 54.99/7.51  
% 54.99/7.51  fof(f63,plain,(
% 54.99/7.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 54.99/7.51    inference(flattening,[],[f62])).
% 54.99/7.51  
% 54.99/7.51  fof(f93,plain,(
% 54.99/7.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 54.99/7.51    inference(nnf_transformation,[],[f63])).
% 54.99/7.51  
% 54.99/7.51  fof(f94,plain,(
% 54.99/7.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 54.99/7.51    inference(flattening,[],[f93])).
% 54.99/7.51  
% 54.99/7.51  fof(f98,plain,(
% 54.99/7.51    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK9 = X2 & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK9))) )),
% 54.99/7.51    introduced(choice_axiom,[])).
% 54.99/7.51  
% 54.99/7.51  fof(f97,plain,(
% 54.99/7.51    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK8,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK8,X0,X1)) & sK8 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 54.99/7.51    introduced(choice_axiom,[])).
% 54.99/7.51  
% 54.99/7.51  fof(f96,plain,(
% 54.99/7.51    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v5_pre_topc(X2,X0,sK7)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(X2,X0,sK7)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK7)) & v1_funct_1(X2)) & l1_pre_topc(sK7) & v2_pre_topc(sK7))) )),
% 54.99/7.51    introduced(choice_axiom,[])).
% 54.99/7.51  
% 54.99/7.51  fof(f95,plain,(
% 54.99/7.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK6,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK6,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 54.99/7.51    introduced(choice_axiom,[])).
% 54.99/7.51  
% 54.99/7.51  fof(f99,plain,(
% 54.99/7.51    ((((~v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v5_pre_topc(sK8,sK6,sK7)) & (v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,sK6,sK7)) & sK8 = sK9 & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) & v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) & v1_funct_1(sK9)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(sK8)) & l1_pre_topc(sK7) & v2_pre_topc(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 54.99/7.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f94,f98,f97,f96,f95])).
% 54.99/7.51  
% 54.99/7.51  fof(f167,plain,(
% 54.99/7.51    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 54.99/7.51    inference(cnf_transformation,[],[f99])).
% 54.99/7.51  
% 54.99/7.51  fof(f171,plain,(
% 54.99/7.51    sK8 = sK9),
% 54.99/7.51    inference(cnf_transformation,[],[f99])).
% 54.99/7.51  
% 54.99/7.51  fof(f20,axiom,(
% 54.99/7.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f48,plain,(
% 54.99/7.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 54.99/7.51    inference(ennf_transformation,[],[f20])).
% 54.99/7.51  
% 54.99/7.51  fof(f49,plain,(
% 54.99/7.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 54.99/7.51    inference(flattening,[],[f48])).
% 54.99/7.51  
% 54.99/7.51  fof(f80,plain,(
% 54.99/7.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 54.99/7.51    inference(nnf_transformation,[],[f49])).
% 54.99/7.51  
% 54.99/7.51  fof(f134,plain,(
% 54.99/7.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 54.99/7.51    inference(cnf_transformation,[],[f80])).
% 54.99/7.51  
% 54.99/7.51  fof(f16,axiom,(
% 54.99/7.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f42,plain,(
% 54.99/7.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 54.99/7.51    inference(ennf_transformation,[],[f16])).
% 54.99/7.51  
% 54.99/7.51  fof(f127,plain,(
% 54.99/7.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 54.99/7.51    inference(cnf_transformation,[],[f42])).
% 54.99/7.51  
% 54.99/7.51  fof(f166,plain,(
% 54.99/7.51    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))),
% 54.99/7.51    inference(cnf_transformation,[],[f99])).
% 54.99/7.51  
% 54.99/7.51  fof(f11,axiom,(
% 54.99/7.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f79,plain,(
% 54.99/7.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 54.99/7.51    inference(nnf_transformation,[],[f11])).
% 54.99/7.51  
% 54.99/7.51  fof(f122,plain,(
% 54.99/7.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f79])).
% 54.99/7.51  
% 54.99/7.51  fof(f170,plain,(
% 54.99/7.51    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))),
% 54.99/7.51    inference(cnf_transformation,[],[f99])).
% 54.99/7.51  
% 54.99/7.51  fof(f27,axiom,(
% 54.99/7.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f60,plain,(
% 54.99/7.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 54.99/7.51    inference(ennf_transformation,[],[f27])).
% 54.99/7.51  
% 54.99/7.51  fof(f61,plain,(
% 54.99/7.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 54.99/7.51    inference(flattening,[],[f60])).
% 54.99/7.51  
% 54.99/7.51  fof(f92,plain,(
% 54.99/7.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 54.99/7.51    inference(nnf_transformation,[],[f61])).
% 54.99/7.51  
% 54.99/7.51  fof(f159,plain,(
% 54.99/7.51    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f92])).
% 54.99/7.51  
% 54.99/7.51  fof(f190,plain,(
% 54.99/7.51    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 54.99/7.51    inference(equality_resolution,[],[f159])).
% 54.99/7.51  
% 54.99/7.51  fof(f161,plain,(
% 54.99/7.51    v2_pre_topc(sK6)),
% 54.99/7.51    inference(cnf_transformation,[],[f99])).
% 54.99/7.51  
% 54.99/7.51  fof(f162,plain,(
% 54.99/7.51    l1_pre_topc(sK6)),
% 54.99/7.51    inference(cnf_transformation,[],[f99])).
% 54.99/7.51  
% 54.99/7.51  fof(f163,plain,(
% 54.99/7.51    v2_pre_topc(sK7)),
% 54.99/7.51    inference(cnf_transformation,[],[f99])).
% 54.99/7.51  
% 54.99/7.51  fof(f164,plain,(
% 54.99/7.51    l1_pre_topc(sK7)),
% 54.99/7.51    inference(cnf_transformation,[],[f99])).
% 54.99/7.51  
% 54.99/7.51  fof(f168,plain,(
% 54.99/7.51    v1_funct_1(sK9)),
% 54.99/7.51    inference(cnf_transformation,[],[f99])).
% 54.99/7.51  
% 54.99/7.51  fof(f169,plain,(
% 54.99/7.51    v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))),
% 54.99/7.51    inference(cnf_transformation,[],[f99])).
% 54.99/7.51  
% 54.99/7.51  fof(f23,axiom,(
% 54.99/7.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f31,plain,(
% 54.99/7.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 54.99/7.51    inference(pure_predicate_removal,[],[f23])).
% 54.99/7.51  
% 54.99/7.51  fof(f54,plain,(
% 54.99/7.51    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 54.99/7.51    inference(ennf_transformation,[],[f31])).
% 54.99/7.51  
% 54.99/7.51  fof(f154,plain,(
% 54.99/7.51    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 54.99/7.51    inference(cnf_transformation,[],[f54])).
% 54.99/7.51  
% 54.99/7.51  fof(f24,axiom,(
% 54.99/7.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f55,plain,(
% 54.99/7.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.99/7.51    inference(ennf_transformation,[],[f24])).
% 54.99/7.51  
% 54.99/7.51  fof(f155,plain,(
% 54.99/7.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f55])).
% 54.99/7.51  
% 54.99/7.51  fof(f25,axiom,(
% 54.99/7.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f32,plain,(
% 54.99/7.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 54.99/7.51    inference(pure_predicate_removal,[],[f25])).
% 54.99/7.51  
% 54.99/7.51  fof(f56,plain,(
% 54.99/7.51    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 54.99/7.51    inference(ennf_transformation,[],[f32])).
% 54.99/7.51  
% 54.99/7.51  fof(f57,plain,(
% 54.99/7.51    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 54.99/7.51    inference(flattening,[],[f56])).
% 54.99/7.51  
% 54.99/7.51  fof(f156,plain,(
% 54.99/7.51    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f57])).
% 54.99/7.51  
% 54.99/7.51  fof(f173,plain,(
% 54.99/7.51    ~v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v5_pre_topc(sK8,sK6,sK7)),
% 54.99/7.51    inference(cnf_transformation,[],[f99])).
% 54.99/7.51  
% 54.99/7.51  fof(f26,axiom,(
% 54.99/7.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f58,plain,(
% 54.99/7.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 54.99/7.51    inference(ennf_transformation,[],[f26])).
% 54.99/7.51  
% 54.99/7.51  fof(f59,plain,(
% 54.99/7.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 54.99/7.51    inference(flattening,[],[f58])).
% 54.99/7.51  
% 54.99/7.51  fof(f91,plain,(
% 54.99/7.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 54.99/7.51    inference(nnf_transformation,[],[f59])).
% 54.99/7.51  
% 54.99/7.51  fof(f158,plain,(
% 54.99/7.51    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f91])).
% 54.99/7.51  
% 54.99/7.51  fof(f187,plain,(
% 54.99/7.51    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 54.99/7.51    inference(equality_resolution,[],[f158])).
% 54.99/7.51  
% 54.99/7.51  fof(f172,plain,(
% 54.99/7.51    v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,sK6,sK7)),
% 54.99/7.51    inference(cnf_transformation,[],[f99])).
% 54.99/7.51  
% 54.99/7.51  fof(f160,plain,(
% 54.99/7.51    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f92])).
% 54.99/7.51  
% 54.99/7.51  fof(f189,plain,(
% 54.99/7.51    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 54.99/7.51    inference(equality_resolution,[],[f160])).
% 54.99/7.51  
% 54.99/7.51  fof(f157,plain,(
% 54.99/7.51    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f91])).
% 54.99/7.51  
% 54.99/7.51  fof(f188,plain,(
% 54.99/7.51    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 54.99/7.51    inference(equality_resolution,[],[f157])).
% 54.99/7.51  
% 54.99/7.51  fof(f2,axiom,(
% 54.99/7.51    v1_xboole_0(k1_xboole_0)),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f102,plain,(
% 54.99/7.51    v1_xboole_0(k1_xboole_0)),
% 54.99/7.51    inference(cnf_transformation,[],[f2])).
% 54.99/7.51  
% 54.99/7.51  fof(f5,axiom,(
% 54.99/7.51    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f34,plain,(
% 54.99/7.51    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 54.99/7.51    inference(ennf_transformation,[],[f5])).
% 54.99/7.51  
% 54.99/7.51  fof(f107,plain,(
% 54.99/7.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f34])).
% 54.99/7.51  
% 54.99/7.51  fof(f14,axiom,(
% 54.99/7.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f40,plain,(
% 54.99/7.51    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 54.99/7.51    inference(ennf_transformation,[],[f14])).
% 54.99/7.51  
% 54.99/7.51  fof(f125,plain,(
% 54.99/7.51    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f40])).
% 54.99/7.51  
% 54.99/7.51  fof(f18,axiom,(
% 54.99/7.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f44,plain,(
% 54.99/7.51    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 54.99/7.51    inference(ennf_transformation,[],[f18])).
% 54.99/7.51  
% 54.99/7.51  fof(f45,plain,(
% 54.99/7.51    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 54.99/7.51    inference(flattening,[],[f44])).
% 54.99/7.51  
% 54.99/7.51  fof(f130,plain,(
% 54.99/7.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 54.99/7.51    inference(cnf_transformation,[],[f45])).
% 54.99/7.51  
% 54.99/7.51  fof(f21,axiom,(
% 54.99/7.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f50,plain,(
% 54.99/7.51    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 54.99/7.51    inference(ennf_transformation,[],[f21])).
% 54.99/7.51  
% 54.99/7.51  fof(f51,plain,(
% 54.99/7.51    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 54.99/7.51    inference(flattening,[],[f50])).
% 54.99/7.51  
% 54.99/7.51  fof(f140,plain,(
% 54.99/7.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f51])).
% 54.99/7.51  
% 54.99/7.51  fof(f19,axiom,(
% 54.99/7.51    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f46,plain,(
% 54.99/7.51    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 54.99/7.51    inference(ennf_transformation,[],[f19])).
% 54.99/7.51  
% 54.99/7.51  fof(f47,plain,(
% 54.99/7.51    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 54.99/7.51    inference(flattening,[],[f46])).
% 54.99/7.51  
% 54.99/7.51  fof(f132,plain,(
% 54.99/7.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f47])).
% 54.99/7.51  
% 54.99/7.51  fof(f3,axiom,(
% 54.99/7.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f33,plain,(
% 54.99/7.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 54.99/7.51    inference(ennf_transformation,[],[f3])).
% 54.99/7.51  
% 54.99/7.51  fof(f103,plain,(
% 54.99/7.51    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f33])).
% 54.99/7.51  
% 54.99/7.51  fof(f121,plain,(
% 54.99/7.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 54.99/7.51    inference(cnf_transformation,[],[f79])).
% 54.99/7.51  
% 54.99/7.51  fof(f10,axiom,(
% 54.99/7.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f120,plain,(
% 54.99/7.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 54.99/7.51    inference(cnf_transformation,[],[f10])).
% 54.99/7.51  
% 54.99/7.51  fof(f7,axiom,(
% 54.99/7.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f76,plain,(
% 54.99/7.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 54.99/7.51    inference(nnf_transformation,[],[f7])).
% 54.99/7.51  
% 54.99/7.51  fof(f77,plain,(
% 54.99/7.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 54.99/7.51    inference(flattening,[],[f76])).
% 54.99/7.51  
% 54.99/7.51  fof(f112,plain,(
% 54.99/7.51    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f77])).
% 54.99/7.51  
% 54.99/7.51  fof(f113,plain,(
% 54.99/7.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 54.99/7.51    inference(cnf_transformation,[],[f77])).
% 54.99/7.51  
% 54.99/7.51  fof(f180,plain,(
% 54.99/7.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 54.99/7.51    inference(equality_resolution,[],[f113])).
% 54.99/7.51  
% 54.99/7.51  fof(f114,plain,(
% 54.99/7.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 54.99/7.51    inference(cnf_transformation,[],[f77])).
% 54.99/7.51  
% 54.99/7.51  fof(f179,plain,(
% 54.99/7.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 54.99/7.51    inference(equality_resolution,[],[f114])).
% 54.99/7.51  
% 54.99/7.51  fof(f17,axiom,(
% 54.99/7.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f43,plain,(
% 54.99/7.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 54.99/7.51    inference(ennf_transformation,[],[f17])).
% 54.99/7.51  
% 54.99/7.51  fof(f128,plain,(
% 54.99/7.51    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 54.99/7.51    inference(cnf_transformation,[],[f43])).
% 54.99/7.51  
% 54.99/7.51  fof(f1,axiom,(
% 54.99/7.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f66,plain,(
% 54.99/7.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 54.99/7.51    inference(nnf_transformation,[],[f1])).
% 54.99/7.51  
% 54.99/7.51  fof(f67,plain,(
% 54.99/7.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 54.99/7.51    inference(rectify,[],[f66])).
% 54.99/7.51  
% 54.99/7.51  fof(f68,plain,(
% 54.99/7.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 54.99/7.51    introduced(choice_axiom,[])).
% 54.99/7.51  
% 54.99/7.51  fof(f69,plain,(
% 54.99/7.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 54.99/7.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f67,f68])).
% 54.99/7.51  
% 54.99/7.51  fof(f101,plain,(
% 54.99/7.51    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f69])).
% 54.99/7.51  
% 54.99/7.51  fof(f15,axiom,(
% 54.99/7.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f41,plain,(
% 54.99/7.51    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 54.99/7.51    inference(ennf_transformation,[],[f15])).
% 54.99/7.51  
% 54.99/7.51  fof(f126,plain,(
% 54.99/7.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 54.99/7.51    inference(cnf_transformation,[],[f41])).
% 54.99/7.51  
% 54.99/7.51  fof(f12,axiom,(
% 54.99/7.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f37,plain,(
% 54.99/7.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 54.99/7.51    inference(ennf_transformation,[],[f12])).
% 54.99/7.51  
% 54.99/7.51  fof(f38,plain,(
% 54.99/7.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 54.99/7.51    inference(flattening,[],[f37])).
% 54.99/7.51  
% 54.99/7.51  fof(f123,plain,(
% 54.99/7.51    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f38])).
% 54.99/7.51  
% 54.99/7.51  fof(f8,axiom,(
% 54.99/7.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 54.99/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.99/7.51  
% 54.99/7.51  fof(f35,plain,(
% 54.99/7.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 54.99/7.51    inference(ennf_transformation,[],[f8])).
% 54.99/7.51  
% 54.99/7.51  fof(f78,plain,(
% 54.99/7.51    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 54.99/7.51    inference(nnf_transformation,[],[f35])).
% 54.99/7.51  
% 54.99/7.51  fof(f115,plain,(
% 54.99/7.51    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 54.99/7.51    inference(cnf_transformation,[],[f78])).
% 54.99/7.51  
% 54.99/7.51  cnf(c_67,negated_conjecture,
% 54.99/7.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
% 54.99/7.51      inference(cnf_transformation,[],[f167]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5068,plain,
% 54.99/7.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_63,negated_conjecture,
% 54.99/7.51      ( sK8 = sK9 ),
% 54.99/7.51      inference(cnf_transformation,[],[f171]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5128,plain,
% 54.99/7.51      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
% 54.99/7.51      inference(light_normalisation,[status(thm)],[c_5068,c_63]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_39,plain,
% 54.99/7.51      ( ~ v1_funct_2(X0,X1,X2)
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 54.99/7.51      | k1_relset_1(X1,X2,X0) = X1
% 54.99/7.51      | k1_xboole_0 = X2 ),
% 54.99/7.51      inference(cnf_transformation,[],[f134]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5095,plain,
% 54.99/7.51      ( k1_relset_1(X0,X1,X2) = X0
% 54.99/7.51      | k1_xboole_0 = X1
% 54.99/7.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 54.99/7.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_14982,plain,
% 54.99/7.51      ( k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9) = u1_struct_0(sK6)
% 54.99/7.51      | u1_struct_0(sK7) = k1_xboole_0
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5128,c_5095]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_27,plain,
% 54.99/7.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 54.99/7.51      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 54.99/7.51      inference(cnf_transformation,[],[f127]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5104,plain,
% 54.99/7.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 54.99/7.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8099,plain,
% 54.99/7.51      ( k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK9) = k1_relat_1(sK9) ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5128,c_5104]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_14985,plain,
% 54.99/7.51      ( u1_struct_0(sK7) = k1_xboole_0
% 54.99/7.51      | u1_struct_0(sK6) = k1_relat_1(sK9)
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top ),
% 54.99/7.51      inference(light_normalisation,[status(thm)],[c_14982,c_8099]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_68,negated_conjecture,
% 54.99/7.51      ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
% 54.99/7.51      inference(cnf_transformation,[],[f166]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5067,plain,
% 54.99/7.51      ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5127,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
% 54.99/7.51      inference(light_normalisation,[status(thm)],[c_5067,c_63]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_15125,plain,
% 54.99/7.51      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 54.99/7.51      | u1_struct_0(sK7) = k1_xboole_0 ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_14985,c_5127]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_15126,plain,
% 54.99/7.51      ( u1_struct_0(sK7) = k1_xboole_0
% 54.99/7.51      | u1_struct_0(sK6) = k1_relat_1(sK9) ),
% 54.99/7.51      inference(renaming,[status(thm)],[c_15125]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_21,plain,
% 54.99/7.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 54.99/7.51      inference(cnf_transformation,[],[f122]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5110,plain,
% 54.99/7.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 54.99/7.51      | r1_tarski(X0,X1) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_64,negated_conjecture,
% 54.99/7.51      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) ),
% 54.99/7.51      inference(cnf_transformation,[],[f170]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5071,plain,
% 54.99/7.51      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_60,plain,
% 54.99/7.51      ( ~ v5_pre_topc(X0,X1,X2)
% 54.99/7.51      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 54.99/7.51      | ~ l1_pre_topc(X1)
% 54.99/7.51      | ~ l1_pre_topc(X2)
% 54.99/7.51      | ~ v2_pre_topc(X1)
% 54.99/7.51      | ~ v2_pre_topc(X2)
% 54.99/7.51      | ~ v1_funct_1(X0) ),
% 54.99/7.51      inference(cnf_transformation,[],[f190]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5074,plain,
% 54.99/7.51      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 54.99/7.51      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 54.99/7.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 54.99/7.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 54.99/7.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 54.99/7.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 54.99/7.51      | l1_pre_topc(X1) != iProver_top
% 54.99/7.51      | l1_pre_topc(X2) != iProver_top
% 54.99/7.51      | v2_pre_topc(X1) != iProver_top
% 54.99/7.51      | v2_pre_topc(X2) != iProver_top
% 54.99/7.51      | v1_funct_1(X0) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_6105,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 54.99/7.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 54.99/7.51      | l1_pre_topc(sK7) != iProver_top
% 54.99/7.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 54.99/7.51      | v2_pre_topc(sK7) != iProver_top
% 54.99/7.51      | v1_funct_1(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5071,c_5074]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_73,negated_conjecture,
% 54.99/7.51      ( v2_pre_topc(sK6) ),
% 54.99/7.51      inference(cnf_transformation,[],[f161]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_74,plain,
% 54.99/7.51      ( v2_pre_topc(sK6) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_72,negated_conjecture,
% 54.99/7.51      ( l1_pre_topc(sK6) ),
% 54.99/7.51      inference(cnf_transformation,[],[f162]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_75,plain,
% 54.99/7.51      ( l1_pre_topc(sK6) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_72]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_71,negated_conjecture,
% 54.99/7.51      ( v2_pre_topc(sK7) ),
% 54.99/7.51      inference(cnf_transformation,[],[f163]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_76,plain,
% 54.99/7.51      ( v2_pre_topc(sK7) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_70,negated_conjecture,
% 54.99/7.51      ( l1_pre_topc(sK7) ),
% 54.99/7.51      inference(cnf_transformation,[],[f164]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_77,plain,
% 54.99/7.51      ( l1_pre_topc(sK7) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_70]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_66,negated_conjecture,
% 54.99/7.51      ( v1_funct_1(sK9) ),
% 54.99/7.51      inference(cnf_transformation,[],[f168]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_81,plain,
% 54.99/7.51      ( v1_funct_1(sK9) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_65,negated_conjecture,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) ),
% 54.99/7.51      inference(cnf_transformation,[],[f169]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_82,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_54,plain,
% 54.99/7.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 54.99/7.51      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 54.99/7.51      inference(cnf_transformation,[],[f154]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5324,plain,
% 54.99/7.51      ( ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
% 54.99/7.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_54]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5325,plain,
% 54.99/7.51      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top
% 54.99/7.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_5324]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_55,plain,
% 54.99/7.51      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 54.99/7.51      | ~ l1_pre_topc(X0) ),
% 54.99/7.51      inference(cnf_transformation,[],[f155]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5664,plain,
% 54.99/7.51      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
% 54.99/7.51      | ~ l1_pre_topc(sK6) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_55]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5665,plain,
% 54.99/7.51      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top
% 54.99/7.51      | l1_pre_topc(sK6) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_5664]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_56,plain,
% 54.99/7.51      ( ~ l1_pre_topc(X0)
% 54.99/7.51      | ~ v2_pre_topc(X0)
% 54.99/7.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 54.99/7.51      inference(cnf_transformation,[],[f156]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5810,plain,
% 54.99/7.51      ( ~ l1_pre_topc(sK6)
% 54.99/7.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 54.99/7.51      | ~ v2_pre_topc(sK6) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_56]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5811,plain,
% 54.99/7.51      ( l1_pre_topc(sK6) != iProver_top
% 54.99/7.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 54.99/7.51      | v2_pre_topc(sK6) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_5810]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_6151,plain,
% 54.99/7.51      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_6105,c_74,c_75,c_76,c_77,c_81,c_82,c_5325,c_5665,
% 54.99/7.51                 c_5811]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_6152,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
% 54.99/7.51      inference(renaming,[status(thm)],[c_6151]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_7036,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5110,c_6152]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_15199,plain,
% 54.99/7.51      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_15126,c_7036]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_61,negated_conjecture,
% 54.99/7.51      ( ~ v5_pre_topc(sK8,sK6,sK7)
% 54.99/7.51      | ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
% 54.99/7.51      inference(cnf_transformation,[],[f173]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5073,plain,
% 54.99/7.51      ( v5_pre_topc(sK8,sK6,sK7) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5131,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,sK7) != iProver_top ),
% 54.99/7.51      inference(light_normalisation,[status(thm)],[c_5073,c_63]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_7043,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_7036,c_5131]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_57,plain,
% 54.99/7.51      ( v5_pre_topc(X0,X1,X2)
% 54.99/7.51      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 54.99/7.51      | ~ l1_pre_topc(X1)
% 54.99/7.51      | ~ l1_pre_topc(X2)
% 54.99/7.51      | ~ v2_pre_topc(X1)
% 54.99/7.51      | ~ v2_pre_topc(X2)
% 54.99/7.51      | ~ v1_funct_1(X0) ),
% 54.99/7.51      inference(cnf_transformation,[],[f187]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5895,plain,
% 54.99/7.51      ( v5_pre_topc(X0,X1,sK7)
% 54.99/7.51      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),sK7)
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK7))
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(sK7))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK7))))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(sK7))))
% 54.99/7.51      | ~ l1_pre_topc(X1)
% 54.99/7.51      | ~ l1_pre_topc(sK7)
% 54.99/7.51      | ~ v2_pre_topc(X1)
% 54.99/7.51      | ~ v2_pre_topc(sK7)
% 54.99/7.51      | ~ v1_funct_1(X0) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_57]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8113,plain,
% 54.99/7.51      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
% 54.99/7.51      | v5_pre_topc(X0,sK6,sK7)
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 54.99/7.51      | ~ l1_pre_topc(sK7)
% 54.99/7.51      | ~ l1_pre_topc(sK6)
% 54.99/7.51      | ~ v2_pre_topc(sK7)
% 54.99/7.51      | ~ v2_pre_topc(sK6)
% 54.99/7.51      | ~ v1_funct_1(X0) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_5895]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8898,plain,
% 54.99/7.51      ( ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
% 54.99/7.51      | v5_pre_topc(sK9,sK6,sK7)
% 54.99/7.51      | ~ v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
% 54.99/7.51      | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7))
% 54.99/7.51      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
% 54.99/7.51      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 54.99/7.51      | ~ l1_pre_topc(sK7)
% 54.99/7.51      | ~ l1_pre_topc(sK6)
% 54.99/7.51      | ~ v2_pre_topc(sK7)
% 54.99/7.51      | ~ v2_pre_topc(sK6)
% 54.99/7.51      | ~ v1_funct_1(sK9) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_8113]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8899,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 54.99/7.51      | l1_pre_topc(sK7) != iProver_top
% 54.99/7.51      | l1_pre_topc(sK6) != iProver_top
% 54.99/7.51      | v2_pre_topc(sK7) != iProver_top
% 54.99/7.51      | v2_pre_topc(sK6) != iProver_top
% 54.99/7.51      | v1_funct_1(sK9) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_8898]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_59841,plain,
% 54.99/7.51      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 54.99/7.51      | ~ r1_tarski(sK9,k2_zfmisc_1(X0,X1)) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_21]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_77716,plain,
% 54.99/7.51      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
% 54.99/7.51      | ~ r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_59841]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_77717,plain,
% 54.99/7.51      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) = iProver_top
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_77716]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_139118,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_15199,c_74,c_75,c_76,c_77,c_81,c_5127,c_5128,c_7043,
% 54.99/7.51                 c_8899,c_77717]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_62,negated_conjecture,
% 54.99/7.51      ( v5_pre_topc(sK8,sK6,sK7)
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
% 54.99/7.51      inference(cnf_transformation,[],[f172]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5072,plain,
% 54.99/7.51      ( v5_pre_topc(sK8,sK6,sK7) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5130,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,sK7) = iProver_top ),
% 54.99/7.51      inference(light_normalisation,[status(thm)],[c_5072,c_63]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_59,plain,
% 54.99/7.51      ( v5_pre_topc(X0,X1,X2)
% 54.99/7.51      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 54.99/7.51      | ~ l1_pre_topc(X1)
% 54.99/7.51      | ~ l1_pre_topc(X2)
% 54.99/7.51      | ~ v2_pre_topc(X1)
% 54.99/7.51      | ~ v2_pre_topc(X2)
% 54.99/7.51      | ~ v1_funct_1(X0) ),
% 54.99/7.51      inference(cnf_transformation,[],[f189]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5075,plain,
% 54.99/7.51      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 54.99/7.51      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 54.99/7.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 54.99/7.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 54.99/7.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 54.99/7.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 54.99/7.51      | l1_pre_topc(X1) != iProver_top
% 54.99/7.51      | l1_pre_topc(X2) != iProver_top
% 54.99/7.51      | v2_pre_topc(X1) != iProver_top
% 54.99/7.51      | v2_pre_topc(X2) != iProver_top
% 54.99/7.51      | v1_funct_1(X0) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_6310,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 54.99/7.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 54.99/7.51      | l1_pre_topc(sK7) != iProver_top
% 54.99/7.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 54.99/7.51      | v2_pre_topc(sK7) != iProver_top
% 54.99/7.51      | v1_funct_1(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5071,c_5075]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_6779,plain,
% 54.99/7.51      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_6310,c_74,c_75,c_76,c_77,c_81,c_82,c_5325,c_5665,
% 54.99/7.51                 c_5811]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_6780,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
% 54.99/7.51      inference(renaming,[status(thm)],[c_6779]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_6783,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5130,c_6780]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_58,plain,
% 54.99/7.51      ( ~ v5_pre_topc(X0,X1,X2)
% 54.99/7.51      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 54.99/7.51      | ~ l1_pre_topc(X1)
% 54.99/7.51      | ~ l1_pre_topc(X2)
% 54.99/7.51      | ~ v2_pre_topc(X1)
% 54.99/7.51      | ~ v2_pre_topc(X2)
% 54.99/7.51      | ~ v1_funct_1(X0) ),
% 54.99/7.51      inference(cnf_transformation,[],[f188]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_14056,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),X0)
% 54.99/7.51      | ~ v5_pre_topc(sK9,sK6,X0)
% 54.99/7.51      | ~ v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(X0))
% 54.99/7.51      | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(X0))
% 54.99/7.51      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(X0))))
% 54.99/7.51      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0))))
% 54.99/7.51      | ~ l1_pre_topc(X0)
% 54.99/7.51      | ~ l1_pre_topc(sK6)
% 54.99/7.51      | ~ v2_pre_topc(X0)
% 54.99/7.51      | ~ v2_pre_topc(sK6)
% 54.99/7.51      | ~ v1_funct_1(sK9) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_58]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_34373,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
% 54.99/7.51      | ~ v5_pre_topc(sK9,sK6,sK7)
% 54.99/7.51      | ~ v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
% 54.99/7.51      | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7))
% 54.99/7.51      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
% 54.99/7.51      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 54.99/7.51      | ~ l1_pre_topc(sK7)
% 54.99/7.51      | ~ l1_pre_topc(sK6)
% 54.99/7.51      | ~ v2_pre_topc(sK7)
% 54.99/7.51      | ~ v2_pre_topc(sK6)
% 54.99/7.51      | ~ v1_funct_1(sK9) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_14056]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_34374,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 54.99/7.51      | l1_pre_topc(sK7) != iProver_top
% 54.99/7.51      | l1_pre_topc(sK6) != iProver_top
% 54.99/7.51      | v2_pre_topc(sK7) != iProver_top
% 54.99/7.51      | v2_pre_topc(sK6) != iProver_top
% 54.99/7.51      | v1_funct_1(sK9) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_34373]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_139122,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_139118,c_74,c_75,c_76,c_77,c_81,c_5127,c_5128,c_6783,
% 54.99/7.51                 c_34374,c_77717]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_79,plain,
% 54.99/7.51      ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_2,plain,
% 54.99/7.51      ( v1_xboole_0(k1_xboole_0) ),
% 54.99/7.51      inference(cnf_transformation,[],[f102]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5136,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) ),
% 54.99/7.51      inference(predicate_to_equality_rev,[status(thm)],[c_5127]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_7,plain,
% 54.99/7.51      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 54.99/7.51      inference(cnf_transformation,[],[f107]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_7359,plain,
% 54.99/7.51      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK9) | sK9 = X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_7]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_7361,plain,
% 54.99/7.51      ( ~ v1_xboole_0(sK9)
% 54.99/7.51      | ~ v1_xboole_0(k1_xboole_0)
% 54.99/7.51      | sK9 = k1_xboole_0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_7359]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8840,plain,
% 54.99/7.51      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK9) | X0 = sK9 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_7]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8842,plain,
% 54.99/7.51      ( ~ v1_xboole_0(sK9)
% 54.99/7.51      | ~ v1_xboole_0(k1_xboole_0)
% 54.99/7.51      | k1_xboole_0 = sK9 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_8840]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_3673,plain,( X0 = X0 ),theory(equality) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_11071,plain,
% 54.99/7.51      ( sK9 = sK9 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3673]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_25,plain,
% 54.99/7.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 54.99/7.51      | ~ v1_xboole_0(X2)
% 54.99/7.51      | v1_xboole_0(X0) ),
% 54.99/7.51      inference(cnf_transformation,[],[f125]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5106,plain,
% 54.99/7.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 54.99/7.51      | v1_xboole_0(X2) != iProver_top
% 54.99/7.51      | v1_xboole_0(X0) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_11162,plain,
% 54.99/7.51      ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | v1_xboole_0(sK9) = iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5071,c_5106]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_11170,plain,
% 54.99/7.51      ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | v1_xboole_0(sK9) ),
% 54.99/7.51      inference(predicate_to_equality_rev,[status(thm)],[c_11162]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_12420,plain,
% 54.99/7.51      ( u1_struct_0(sK7) = u1_struct_0(sK7) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3673]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_29,plain,
% 54.99/7.51      ( v1_funct_2(X0,X1,X2)
% 54.99/7.51      | ~ v1_partfun1(X0,X1)
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 54.99/7.51      | ~ v1_funct_1(X0) ),
% 54.99/7.51      inference(cnf_transformation,[],[f130]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_13300,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
% 54.99/7.51      | ~ v1_partfun1(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 54.99/7.51      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
% 54.99/7.51      | ~ v1_funct_1(sK9) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_29]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_13301,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) = iProver_top
% 54.99/7.51      | v1_partfun1(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 54.99/7.51      | v1_funct_1(sK9) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_13300]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_41,plain,
% 54.99/7.51      ( ~ v1_funct_2(X0,X1,X2)
% 54.99/7.51      | v1_partfun1(X0,X1)
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 54.99/7.51      | ~ v1_funct_1(X0)
% 54.99/7.51      | k1_xboole_0 = X2 ),
% 54.99/7.51      inference(cnf_transformation,[],[f140]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5093,plain,
% 54.99/7.51      ( k1_xboole_0 = X0
% 54.99/7.51      | v1_funct_2(X1,X2,X0) != iProver_top
% 54.99/7.51      | v1_partfun1(X1,X2) = iProver_top
% 54.99/7.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 54.99/7.51      | v1_funct_1(X1) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_15536,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | v1_partfun1(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
% 54.99/7.51      | v1_funct_1(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5071,c_5093]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_15895,plain,
% 54.99/7.51      ( v1_partfun1(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0 ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_15536,c_81,c_82]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_15896,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
% 54.99/7.51      | v1_partfun1(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
% 54.99/7.51      inference(renaming,[status(thm)],[c_15895]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_32,plain,
% 54.99/7.51      ( ~ v1_funct_2(X0,X1,X2)
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 54.99/7.51      | ~ v1_funct_1(X0)
% 54.99/7.51      | ~ v1_xboole_0(X0)
% 54.99/7.51      | v1_xboole_0(X1)
% 54.99/7.51      | v1_xboole_0(X2) ),
% 54.99/7.51      inference(cnf_transformation,[],[f132]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5101,plain,
% 54.99/7.51      ( v1_funct_2(X0,X1,X2) != iProver_top
% 54.99/7.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 54.99/7.51      | v1_funct_1(X0) != iProver_top
% 54.99/7.51      | v1_xboole_0(X0) != iProver_top
% 54.99/7.51      | v1_xboole_0(X1) = iProver_top
% 54.99/7.51      | v1_xboole_0(X2) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_16072,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | v1_funct_1(sK9) != iProver_top
% 54.99/7.51      | v1_xboole_0(u1_struct_0(sK7)) = iProver_top
% 54.99/7.51      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top
% 54.99/7.51      | v1_xboole_0(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5128,c_5101]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_16082,plain,
% 54.99/7.51      ( ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7))
% 54.99/7.51      | ~ v1_funct_1(sK9)
% 54.99/7.51      | v1_xboole_0(u1_struct_0(sK7))
% 54.99/7.51      | v1_xboole_0(u1_struct_0(sK6))
% 54.99/7.51      | ~ v1_xboole_0(sK9) ),
% 54.99/7.51      inference(predicate_to_equality_rev,[status(thm)],[c_16072]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_3674,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_9494,plain,
% 54.99/7.51      ( X0 != X1 | X0 = sK8 | sK8 != X1 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3674]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_39482,plain,
% 54.99/7.51      ( X0 = sK8 | X0 != sK9 | sK8 != sK9 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_9494]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_39483,plain,
% 54.99/7.51      ( sK8 != sK9 | k1_xboole_0 = sK8 | k1_xboole_0 != sK9 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_39482]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_3675,plain,
% 54.99/7.51      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 54.99/7.51      theory(equality) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_60070,plain,
% 54.99/7.51      ( ~ v1_xboole_0(X0)
% 54.99/7.51      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3675]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_60080,plain,
% 54.99/7.51      ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | ~ v1_xboole_0(k1_xboole_0)
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != k1_xboole_0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_60070]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_3682,plain,
% 54.99/7.51      ( ~ v1_funct_2(X0,X1,X2)
% 54.99/7.51      | v1_funct_2(X3,X4,X5)
% 54.99/7.51      | X3 != X0
% 54.99/7.51      | X4 != X1
% 54.99/7.51      | X5 != X2 ),
% 54.99/7.51      theory(equality) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_59378,plain,
% 54.99/7.51      ( ~ v1_funct_2(X0,X1,X2)
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != X1
% 54.99/7.51      | u1_struct_0(sK7) != X2
% 54.99/7.51      | sK9 != X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3682]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_62312,plain,
% 54.99/7.51      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK7))
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != X1
% 54.99/7.51      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 54.99/7.51      | sK9 != X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_59378]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_62313,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != X0
% 54.99/7.51      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 54.99/7.51      | sK9 != X1
% 54.99/7.51      | v1_funct_2(X1,X0,u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_62312]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_62315,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != k1_xboole_0
% 54.99/7.51      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 54.99/7.51      | sK9 != k1_xboole_0
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) = iProver_top
% 54.99/7.51      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK7)) != iProver_top ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_62313]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_64178,plain,
% 54.99/7.51      ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | ~ v1_xboole_0(u1_struct_0(sK7))
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_7]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_64436,plain,
% 54.99/7.51      ( ~ v1_xboole_0(X0)
% 54.99/7.51      | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_7]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_64439,plain,
% 54.99/7.51      ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 54.99/7.51      | ~ v1_xboole_0(k1_xboole_0)
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_64436]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_64099,plain,
% 54.99/7.51      ( v1_funct_2(X0,X1,X2)
% 54.99/7.51      | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
% 54.99/7.51      | X2 != u1_struct_0(sK7)
% 54.99/7.51      | X1 != u1_struct_0(sK6)
% 54.99/7.51      | X0 != sK8 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3682]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_70433,plain,
% 54.99/7.51      ( v1_funct_2(X0,X1,u1_struct_0(sK7))
% 54.99/7.51      | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
% 54.99/7.51      | X1 != u1_struct_0(sK6)
% 54.99/7.51      | X0 != sK8
% 54.99/7.51      | u1_struct_0(sK7) != u1_struct_0(sK7) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_64099]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_70434,plain,
% 54.99/7.51      ( X0 != u1_struct_0(sK6)
% 54.99/7.51      | X1 != sK8
% 54.99/7.51      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 54.99/7.51      | v1_funct_2(X1,X0,u1_struct_0(sK7)) = iProver_top
% 54.99/7.51      | v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_70433]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_70436,plain,
% 54.99/7.51      ( u1_struct_0(sK7) != u1_struct_0(sK7)
% 54.99/7.51      | k1_xboole_0 != u1_struct_0(sK6)
% 54.99/7.51      | k1_xboole_0 != sK8
% 54.99/7.51      | v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK7)) = iProver_top ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_70434]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_62298,plain,
% 54.99/7.51      ( X0 != X1 | u1_struct_0(sK7) != X1 | u1_struct_0(sK7) = X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3674]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_67171,plain,
% 54.99/7.51      ( X0 != u1_struct_0(sK7)
% 54.99/7.51      | u1_struct_0(sK7) = X0
% 54.99/7.51      | u1_struct_0(sK7) != u1_struct_0(sK7) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_62298]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_81780,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != u1_struct_0(sK7)
% 54.99/7.51      | u1_struct_0(sK7) = u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
% 54.99/7.51      | u1_struct_0(sK7) != u1_struct_0(sK7) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_67171]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_82222,plain,
% 54.99/7.51      ( ~ v1_xboole_0(X0)
% 54.99/7.51      | ~ v1_xboole_0(u1_struct_0(sK6))
% 54.99/7.51      | X0 = u1_struct_0(sK6) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_7]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_82225,plain,
% 54.99/7.51      ( ~ v1_xboole_0(u1_struct_0(sK6))
% 54.99/7.51      | ~ v1_xboole_0(k1_xboole_0)
% 54.99/7.51      | k1_xboole_0 = u1_struct_0(sK6) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_82222]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_16071,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | v1_funct_1(sK9) != iProver_top
% 54.99/7.51      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top
% 54.99/7.51      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
% 54.99/7.51      | v1_xboole_0(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5071,c_5101]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_16535,plain,
% 54.99/7.51      ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top
% 54.99/7.51      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
% 54.99/7.51      | v1_xboole_0(sK9) != iProver_top ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_16071,c_81,c_82]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_16523,plain,
% 54.99/7.51      ( v1_xboole_0(u1_struct_0(sK7)) = iProver_top
% 54.99/7.51      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top
% 54.99/7.51      | v1_xboole_0(sK9) != iProver_top ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_16072,c_81,c_5127]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5119,plain,
% 54.99/7.51      ( X0 = X1
% 54.99/7.51      | v1_xboole_0(X0) != iProver_top
% 54.99/7.51      | v1_xboole_0(X1) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_16530,plain,
% 54.99/7.51      ( u1_struct_0(sK7) = X0
% 54.99/7.51      | v1_xboole_0(X0) != iProver_top
% 54.99/7.51      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top
% 54.99/7.51      | v1_xboole_0(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_16523,c_5119]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_16730,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7)
% 54.99/7.51      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
% 54.99/7.51      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top
% 54.99/7.51      | v1_xboole_0(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_16535,c_16530]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_3,plain,
% 54.99/7.51      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 54.99/7.51      inference(cnf_transformation,[],[f103]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5122,plain,
% 54.99/7.51      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_17323,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7)
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 54.99/7.51      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top
% 54.99/7.51      | v1_xboole_0(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_16730,c_5122]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_16542,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = X0
% 54.99/7.51      | v1_xboole_0(X0) != iProver_top
% 54.99/7.51      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
% 54.99/7.51      | v1_xboole_0(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_16535,c_5119]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_55798,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7)
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK6)
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 54.99/7.51      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
% 54.99/7.51      | v1_xboole_0(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_17323,c_16542]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_22,plain,
% 54.99/7.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 54.99/7.51      inference(cnf_transformation,[],[f121]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_189,plain,
% 54.99/7.51      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 54.99/7.51      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_22]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_20,plain,
% 54.99/7.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 54.99/7.51      inference(cnf_transformation,[],[f120]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_195,plain,
% 54.99/7.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_20]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_14,plain,
% 54.99/7.51      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 54.99/7.51      | k1_xboole_0 = X0
% 54.99/7.51      | k1_xboole_0 = X1 ),
% 54.99/7.51      inference(cnf_transformation,[],[f112]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_208,plain,
% 54.99/7.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 54.99/7.51      | k1_xboole_0 = k1_xboole_0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_14]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_13,plain,
% 54.99/7.51      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 54.99/7.51      inference(cnf_transformation,[],[f180]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_209,plain,
% 54.99/7.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_13]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_233,plain,
% 54.99/7.51      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_7360,plain,
% 54.99/7.51      ( sK9 = X0
% 54.99/7.51      | v1_xboole_0(X0) != iProver_top
% 54.99/7.51      | v1_xboole_0(sK9) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_7359]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_7362,plain,
% 54.99/7.51      ( sK9 = k1_xboole_0
% 54.99/7.51      | v1_xboole_0(sK9) != iProver_top
% 54.99/7.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_7360]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_15537,plain,
% 54.99/7.51      ( u1_struct_0(sK7) = k1_xboole_0
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | v1_partfun1(sK9,u1_struct_0(sK6)) = iProver_top
% 54.99/7.51      | v1_funct_1(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5128,c_5093]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_15890,plain,
% 54.99/7.51      ( v1_partfun1(sK9,u1_struct_0(sK6)) = iProver_top
% 54.99/7.51      | u1_struct_0(sK7) = k1_xboole_0 ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_15537,c_81,c_5127]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_15891,plain,
% 54.99/7.51      ( u1_struct_0(sK7) = k1_xboole_0
% 54.99/7.51      | v1_partfun1(sK9,u1_struct_0(sK6)) = iProver_top ),
% 54.99/7.51      inference(renaming,[status(thm)],[c_15890]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_15892,plain,
% 54.99/7.51      ( v1_partfun1(sK9,u1_struct_0(sK6))
% 54.99/7.51      | u1_struct_0(sK7) = k1_xboole_0 ),
% 54.99/7.51      inference(predicate_to_equality_rev,[status(thm)],[c_15891]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_16540,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
% 54.99/7.51      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
% 54.99/7.51      | v1_xboole_0(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_16535,c_5122]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_7348,plain,
% 54.99/7.51      ( X0 != X1 | sK9 != X1 | sK9 = X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3674]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_10612,plain,
% 54.99/7.51      ( X0 != sK9 | sK9 = X0 | sK9 != sK9 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_7348]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_26815,plain,
% 54.99/7.51      ( sK8 != sK9 | sK9 = sK8 | sK9 != sK9 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_10612]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_27406,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | ~ v1_partfun1(sK9,u1_struct_0(sK6))
% 54.99/7.51      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
% 54.99/7.51      | ~ v1_funct_1(sK9) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_29]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_14981,plain,
% 54.99/7.51      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),sK9) = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5071,c_5095]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8098,plain,
% 54.99/7.51      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),sK9) = k1_relat_1(sK9) ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5071,c_5104]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_14986,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
% 54.99/7.51      inference(light_normalisation,[status(thm)],[c_14981,c_8098]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_14992,plain,
% 54.99/7.51      ( ~ v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
% 54.99/7.51      inference(predicate_to_equality_rev,[status(thm)],[c_14986]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_17387,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0 ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_14986,c_65,c_14992]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_17388,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
% 54.99/7.51      inference(renaming,[status(thm)],[c_17387]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_17445,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0))) = iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_17388,c_5071]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_12,plain,
% 54.99/7.51      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 54.99/7.51      inference(cnf_transformation,[],[f179]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_17447,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 54.99/7.51      inference(demodulation,[status(thm)],[c_17445,c_12]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_28,plain,
% 54.99/7.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 54.99/7.51      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 54.99/7.51      inference(cnf_transformation,[],[f128]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5103,plain,
% 54.99/7.51      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 54.99/7.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_10195,plain,
% 54.99/7.51      ( k7_relset_1(X0,k1_xboole_0,X1,X2) = k9_relat_1(X1,X2)
% 54.99/7.51      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_12,c_5103]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_17726,plain,
% 54.99/7.51      ( k7_relset_1(X0,k1_xboole_0,sK9,X1) = k9_relat_1(sK9,X1)
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_17447,c_10195]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_34567,plain,
% 54.99/7.51      ( k7_relset_1(X0,k1_xboole_0,sK9,X1) = k9_relat_1(sK9,X1)
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK9),u1_struct_0(sK7)))) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_17726,c_6152]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5077,plain,
% 54.99/7.51      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 54.99/7.51      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 54.99/7.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 54.99/7.51      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 54.99/7.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 54.99/7.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 54.99/7.51      | l1_pre_topc(X1) != iProver_top
% 54.99/7.51      | l1_pre_topc(X2) != iProver_top
% 54.99/7.51      | v2_pre_topc(X1) != iProver_top
% 54.99/7.51      | v2_pre_topc(X2) != iProver_top
% 54.99/7.51      | v1_funct_1(X0) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8087,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 54.99/7.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 54.99/7.51      | l1_pre_topc(sK6) != iProver_top
% 54.99/7.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 54.99/7.51      | v2_pre_topc(sK6) != iProver_top
% 54.99/7.51      | v1_funct_1(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5071,c_5077]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5339,plain,
% 54.99/7.51      ( ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
% 54.99/7.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_54]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5340,plain,
% 54.99/7.51      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
% 54.99/7.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_5339]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5686,plain,
% 54.99/7.51      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
% 54.99/7.51      | ~ l1_pre_topc(sK7) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_55]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5687,plain,
% 54.99/7.51      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top
% 54.99/7.51      | l1_pre_topc(sK7) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_5686]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5842,plain,
% 54.99/7.51      ( ~ l1_pre_topc(sK7)
% 54.99/7.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
% 54.99/7.51      | ~ v2_pre_topc(sK7) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_56]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5843,plain,
% 54.99/7.51      ( l1_pre_topc(sK7) != iProver_top
% 54.99/7.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v2_pre_topc(sK7) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_5842]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8476,plain,
% 54.99/7.51      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_8087,c_74,c_75,c_76,c_77,c_81,c_82,c_5340,c_5687,
% 54.99/7.51                 c_5843]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8477,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
% 54.99/7.51      inference(renaming,[status(thm)],[c_8476]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_35948,plain,
% 54.99/7.51      ( k7_relset_1(X0,k1_xboole_0,sK9,X1) = k9_relat_1(sK9,X1)
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK9),u1_struct_0(sK7)))) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_34567,c_8477]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5076,plain,
% 54.99/7.51      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 54.99/7.51      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 54.99/7.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 54.99/7.51      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 54.99/7.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 54.99/7.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 54.99/7.51      | l1_pre_topc(X1) != iProver_top
% 54.99/7.51      | l1_pre_topc(X2) != iProver_top
% 54.99/7.51      | v2_pre_topc(X1) != iProver_top
% 54.99/7.51      | v2_pre_topc(X2) != iProver_top
% 54.99/7.51      | v1_funct_1(X0) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_7230,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 54.99/7.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 54.99/7.51      | l1_pre_topc(sK6) != iProver_top
% 54.99/7.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 54.99/7.51      | v2_pre_topc(sK6) != iProver_top
% 54.99/7.51      | v1_funct_1(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5071,c_5076]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_7769,plain,
% 54.99/7.51      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_7230,c_74,c_75,c_76,c_77,c_81,c_82,c_5340,c_5687,
% 54.99/7.51                 c_5843]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_7770,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
% 54.99/7.51      inference(renaming,[status(thm)],[c_7769]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8482,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5130,c_8477]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5896,plain,
% 54.99/7.51      ( ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
% 54.99/7.51      | v5_pre_topc(X0,X1,sK7)
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK7))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK7))))
% 54.99/7.51      | ~ l1_pre_topc(X1)
% 54.99/7.51      | ~ l1_pre_topc(sK7)
% 54.99/7.51      | ~ v2_pre_topc(X1)
% 54.99/7.51      | ~ v2_pre_topc(sK7)
% 54.99/7.51      | ~ v1_funct_1(X0) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_59]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8069,plain,
% 54.99/7.51      ( ~ v5_pre_topc(X0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
% 54.99/7.51      | v5_pre_topc(X0,sK6,sK7)
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
% 54.99/7.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 54.99/7.51      | ~ l1_pre_topc(sK7)
% 54.99/7.51      | ~ l1_pre_topc(sK6)
% 54.99/7.51      | ~ v2_pre_topc(sK7)
% 54.99/7.51      | ~ v2_pre_topc(sK6)
% 54.99/7.51      | ~ v1_funct_1(X0) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_5896]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8888,plain,
% 54.99/7.51      ( ~ v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
% 54.99/7.51      | v5_pre_topc(sK9,sK6,sK7)
% 54.99/7.51      | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7))
% 54.99/7.51      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
% 54.99/7.51      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 54.99/7.51      | ~ l1_pre_topc(sK7)
% 54.99/7.51      | ~ l1_pre_topc(sK6)
% 54.99/7.51      | ~ v2_pre_topc(sK7)
% 54.99/7.51      | ~ v2_pre_topc(sK6)
% 54.99/7.51      | ~ v1_funct_1(sK9) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_8069]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8889,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 54.99/7.51      | l1_pre_topc(sK7) != iProver_top
% 54.99/7.51      | l1_pre_topc(sK6) != iProver_top
% 54.99/7.51      | v2_pre_topc(sK7) != iProver_top
% 54.99/7.51      | v2_pre_topc(sK6) != iProver_top
% 54.99/7.51      | v1_funct_1(sK9) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_8888]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_8973,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_8482,c_74,c_75,c_76,c_77,c_81,c_5127,c_5128,c_5130,
% 54.99/7.51                 c_8477,c_8889]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_14085,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,X0,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
% 54.99/7.51      | ~ v5_pre_topc(sK9,X0,sK7)
% 54.99/7.51      | ~ v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | ~ v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7))
% 54.99/7.51      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
% 54.99/7.51      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7))))
% 54.99/7.51      | ~ l1_pre_topc(X0)
% 54.99/7.51      | ~ l1_pre_topc(sK7)
% 54.99/7.51      | ~ v2_pre_topc(X0)
% 54.99/7.51      | ~ v2_pre_topc(sK7)
% 54.99/7.51      | ~ v1_funct_1(sK9) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_60]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_34388,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
% 54.99/7.51      | ~ v5_pre_topc(sK9,sK6,sK7)
% 54.99/7.51      | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7))
% 54.99/7.51      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
% 54.99/7.51      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 54.99/7.51      | ~ l1_pre_topc(sK7)
% 54.99/7.51      | ~ l1_pre_topc(sK6)
% 54.99/7.51      | ~ v2_pre_topc(sK7)
% 54.99/7.51      | ~ v2_pre_topc(sK6)
% 54.99/7.51      | ~ v1_funct_1(sK9) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_14085]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_34389,plain,
% 54.99/7.51      ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 54.99/7.51      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 54.99/7.51      | l1_pre_topc(sK7) != iProver_top
% 54.99/7.51      | l1_pre_topc(sK6) != iProver_top
% 54.99/7.51      | v2_pre_topc(sK7) != iProver_top
% 54.99/7.51      | v2_pre_topc(sK6) != iProver_top
% 54.99/7.51      | v1_funct_1(sK9) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_34388]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_36552,plain,
% 54.99/7.51      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_35948,c_74,c_75,c_76,c_77,c_81,c_5127,c_5128,c_5131,
% 54.99/7.51                 c_7770,c_8973,c_34389]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_36553,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
% 54.99/7.51      inference(renaming,[status(thm)],[c_36552]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_36557,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5110,c_36553]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_36562,plain,
% 54.99/7.51      ( ~ v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | ~ r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) ),
% 54.99/7.51      inference(predicate_to_equality_rev,[status(thm)],[c_36557]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_3677,plain,
% 54.99/7.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 54.99/7.51      theory(equality) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_9054,plain,
% 54.99/7.51      ( ~ r1_tarski(X0,X1) | r1_tarski(sK8,X2) | X2 != X1 | sK8 != X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3677]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_20792,plain,
% 54.99/7.51      ( ~ r1_tarski(X0,X1)
% 54.99/7.51      | r1_tarski(sK8,k2_zfmisc_1(X2,X3))
% 54.99/7.51      | k2_zfmisc_1(X2,X3) != X1
% 54.99/7.51      | sK8 != X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_9054]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_44442,plain,
% 54.99/7.51      ( r1_tarski(sK8,k2_zfmisc_1(X0,X1))
% 54.99/7.51      | ~ r1_tarski(sK9,X2)
% 54.99/7.51      | k2_zfmisc_1(X0,X1) != X2
% 54.99/7.51      | sK8 != sK9 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_20792]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_44444,plain,
% 54.99/7.51      ( r1_tarski(sK8,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 54.99/7.51      | ~ r1_tarski(sK9,k1_xboole_0)
% 54.99/7.51      | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 54.99/7.51      | sK8 != sK9 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_44442]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_50094,plain,
% 54.99/7.51      ( ~ r1_tarski(X0,X1) | r1_tarski(sK9,X2) | X2 != X1 | sK9 != X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3677]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_50096,plain,
% 54.99/7.51      ( r1_tarski(sK9,k1_xboole_0)
% 54.99/7.51      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 54.99/7.51      | sK9 != k1_xboole_0
% 54.99/7.51      | k1_xboole_0 != k1_xboole_0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_50094]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_55800,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7)
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 54.99/7.51      | u1_struct_0(sK6) = k1_xboole_0
% 54.99/7.51      | v1_xboole_0(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_17323,c_5122]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_59630,plain,
% 54.99/7.51      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
% 54.99/7.51      | ~ r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_21]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_60034,plain,
% 54.99/7.51      ( ~ v1_xboole_0(X0)
% 54.99/7.51      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3675]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_60043,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != X0
% 54.99/7.51      | v1_xboole_0(X0) != iProver_top
% 54.99/7.51      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_60034]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_60045,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != k1_xboole_0
% 54.99/7.51      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
% 54.99/7.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_60043]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_64167,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != X0
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7)
% 54.99/7.51      | u1_struct_0(sK7) != X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3674]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_64169,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7)
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != k1_xboole_0
% 54.99/7.51      | u1_struct_0(sK7) != k1_xboole_0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_64167]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_59454,plain,
% 54.99/7.51      ( ~ r1_tarski(X0,X1) | r1_tarski(sK9,X2) | X2 != X1 | sK9 != X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3677]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_62354,plain,
% 54.99/7.51      ( ~ r1_tarski(X0,X1)
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))
% 54.99/7.51      | k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != X1
% 54.99/7.51      | sK9 != X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_59454]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_67238,plain,
% 54.99/7.51      ( ~ r1_tarski(sK8,X0)
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))
% 54.99/7.51      | k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != X0
% 54.99/7.51      | sK9 != sK8 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_62354]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_71324,plain,
% 54.99/7.51      ( ~ r1_tarski(sK8,k2_zfmisc_1(X0,X1))
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))
% 54.99/7.51      | k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != k2_zfmisc_1(X0,X1)
% 54.99/7.51      | sK9 != sK8 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_67238]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_71326,plain,
% 54.99/7.51      ( ~ r1_tarski(sK8,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))
% 54.99/7.51      | k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 54.99/7.51      | sK9 != sK8 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_71324]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_3678,plain,
% 54.99/7.51      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 54.99/7.51      theory(equality) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_93476,plain,
% 54.99/7.51      ( k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = k2_zfmisc_1(X0,X1)
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != X1
% 54.99/7.51      | u1_struct_0(sK6) != X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3678]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_93478,plain,
% 54.99/7.51      ( k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != k1_xboole_0
% 54.99/7.51      | u1_struct_0(sK6) != k1_xboole_0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_93476]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_101751,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7)
% 54.99/7.51      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
% 54.99/7.51      | v1_xboole_0(sK9) != iProver_top ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_55798,c_66,c_63,c_189,c_195,c_208,c_209,c_233,c_7362,
% 54.99/7.51                 c_11071,c_15892,c_16540,c_26815,c_27406,c_36562,c_44444,
% 54.99/7.51                 c_50096,c_55800,c_59630,c_60045,c_64169,c_71326,c_93478]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_101753,plain,
% 54.99/7.51      ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 54.99/7.51      | ~ v1_xboole_0(sK9)
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = u1_struct_0(sK7) ),
% 54.99/7.51      inference(predicate_to_equality_rev,[status(thm)],[c_101751]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_60533,plain,
% 54.99/7.51      ( ~ v1_funct_2(X0,X1,X2)
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(X3),u1_struct_0(X4))
% 54.99/7.51      | u1_struct_0(X3) != X1
% 54.99/7.51      | u1_struct_0(X4) != X2
% 54.99/7.51      | sK9 != X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3682]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_67594,plain,
% 54.99/7.51      ( ~ v1_funct_2(sK9,X0,X1)
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(X2),u1_struct_0(X3))
% 54.99/7.51      | u1_struct_0(X2) != X0
% 54.99/7.51      | u1_struct_0(X3) != X1
% 54.99/7.51      | sK9 != sK9 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_60533]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_79332,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(X1))
% 54.99/7.51      | ~ v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | u1_struct_0(X1) != u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
% 54.99/7.51      | u1_struct_0(X0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 54.99/7.51      | sK9 != sK9 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_67594]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_81775,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7))
% 54.99/7.51      | ~ v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | u1_struct_0(X0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 54.99/7.51      | u1_struct_0(sK7) != u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
% 54.99/7.51      | sK9 != sK9 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_79332]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_107248,plain,
% 54.99/7.51      ( ~ v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 54.99/7.51      | u1_struct_0(sK7) != u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
% 54.99/7.51      | sK9 != sK9 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_81775]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_107249,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 54.99/7.51      | u1_struct_0(sK7) != u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
% 54.99/7.51      | sK9 != sK9
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_107248]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_108410,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3673]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_139126,plain,
% 54.99/7.51      ( r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_139122,c_79,c_66,c_81,c_82,c_63,c_2,c_5136,c_7361,
% 54.99/7.51                 c_8842,c_11071,c_11170,c_12420,c_13301,c_15896,c_16082,
% 54.99/7.51                 c_39483,c_60080,c_62315,c_64178,c_64439,c_70436,c_77717,
% 54.99/7.51                 c_81780,c_82225,c_101753,c_107249,c_108410]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_0,plain,
% 54.99/7.51      ( r2_hidden(sK1(X0),X0) | v1_xboole_0(X0) ),
% 54.99/7.51      inference(cnf_transformation,[],[f101]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5125,plain,
% 54.99/7.51      ( r2_hidden(sK1(X0),X0) = iProver_top
% 54.99/7.51      | v1_xboole_0(X0) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_10193,plain,
% 54.99/7.51      ( k7_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),sK9,X0) = k9_relat_1(sK9,X0) ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5071,c_5103]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_26,plain,
% 54.99/7.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 54.99/7.51      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 54.99/7.51      inference(cnf_transformation,[],[f126]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5105,plain,
% 54.99/7.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 54.99/7.51      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_10973,plain,
% 54.99/7.51      ( m1_subset_1(k9_relat_1(sK9,X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) = iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_10193,c_5105]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_83,plain,
% 54.99/7.51      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_11442,plain,
% 54.99/7.51      ( m1_subset_1(k9_relat_1(sK9,X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) = iProver_top ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_10973,c_83]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_23,plain,
% 54.99/7.51      ( m1_subset_1(X0,X1)
% 54.99/7.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 54.99/7.51      | ~ r2_hidden(X0,X2) ),
% 54.99/7.51      inference(cnf_transformation,[],[f123]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5108,plain,
% 54.99/7.51      ( m1_subset_1(X0,X1) = iProver_top
% 54.99/7.51      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 54.99/7.51      | r2_hidden(X0,X2) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_12174,plain,
% 54.99/7.51      ( m1_subset_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top
% 54.99/7.51      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_11442,c_5108]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_13416,plain,
% 54.99/7.51      ( m1_subset_1(sK1(k9_relat_1(sK9,X0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top
% 54.99/7.51      | v1_xboole_0(k9_relat_1(sK9,X0)) = iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5125,c_12174]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_18,plain,
% 54.99/7.51      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 54.99/7.51      inference(cnf_transformation,[],[f115]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5112,plain,
% 54.99/7.51      ( m1_subset_1(X0,X1) != iProver_top
% 54.99/7.51      | r2_hidden(X0,X1) = iProver_top
% 54.99/7.51      | v1_xboole_0(X1) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_14070,plain,
% 54.99/7.51      ( r2_hidden(sK1(k9_relat_1(sK9,X0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top
% 54.99/7.51      | v1_xboole_0(k9_relat_1(sK9,X0)) = iProver_top
% 54.99/7.51      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_13416,c_5112]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_17417,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 54.99/7.51      | r2_hidden(sK1(k9_relat_1(sK9,X0)),k1_xboole_0) = iProver_top
% 54.99/7.51      | v1_xboole_0(k9_relat_1(sK9,X0)) = iProver_top
% 54.99/7.51      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_17388,c_14070]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_25037,plain,
% 54.99/7.51      ( u1_struct_0(sK6) = u1_struct_0(sK6) ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3673]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_36566,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),k1_xboole_0)) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_17388,c_36557]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_36568,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | r1_tarski(sK9,k1_xboole_0) != iProver_top ),
% 54.99/7.51      inference(demodulation,[status(thm)],[c_36566,c_12]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_36558,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k1_xboole_0))) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_17388,c_36553]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_36560,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 54.99/7.51      inference(demodulation,[status(thm)],[c_36558,c_12]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_37418,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_36568,c_17447,c_36560]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_37419,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
% 54.99/7.51      inference(renaming,[status(thm)],[c_37418]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5102,plain,
% 54.99/7.51      ( v1_funct_2(X0,X1,X2) = iProver_top
% 54.99/7.51      | v1_partfun1(X0,X1) != iProver_top
% 54.99/7.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 54.99/7.51      | v1_funct_1(X0) != iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_15060,plain,
% 54.99/7.51      ( v1_funct_2(X0,X1,k1_xboole_0) = iProver_top
% 54.99/7.51      | v1_partfun1(X0,X1) != iProver_top
% 54.99/7.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 54.99/7.51      | v1_funct_1(X0) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_12,c_5102]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_17730,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 54.99/7.51      | v1_funct_2(sK9,X0,k1_xboole_0) = iProver_top
% 54.99/7.51      | v1_partfun1(sK9,X0) != iProver_top
% 54.99/7.51      | v1_funct_1(sK9) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_17447,c_15060]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_54059,plain,
% 54.99/7.51      ( v1_partfun1(sK9,X0) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,X0,k1_xboole_0) = iProver_top
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_17730,c_81]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_54060,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 54.99/7.51      | v1_funct_2(sK9,X0,k1_xboole_0) = iProver_top
% 54.99/7.51      | v1_partfun1(sK9,X0) != iProver_top ),
% 54.99/7.51      inference(renaming,[status(thm)],[c_54059]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_37422,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),k1_xboole_0) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_17388,c_37419]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_54066,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 54.99/7.51      | v1_partfun1(sK9,u1_struct_0(sK6)) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_54060,c_37422]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_59362,plain,
% 54.99/7.51      ( ~ v1_funct_2(X0,X1,X2)
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != X2
% 54.99/7.51      | u1_struct_0(sK6) != X1
% 54.99/7.51      | sK9 != X0 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_3682]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_62288,plain,
% 54.99/7.51      ( ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 54.99/7.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != u1_struct_0(sK7)
% 54.99/7.51      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 54.99/7.51      | sK9 != sK8 ),
% 54.99/7.51      inference(instantiation,[status(thm)],[c_59362]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_62289,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != u1_struct_0(sK7)
% 54.99/7.51      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 54.99/7.51      | sK9 != sK8
% 54.99/7.51      | v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 54.99/7.51      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_62288]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_65459,plain,
% 54.99/7.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_17417,c_79,c_81,c_65,c_63,c_5127,c_11071,c_14992,
% 54.99/7.51                 c_15537,c_25037,c_26815,c_37419,c_54066,c_62289,c_64169]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_139130,plain,
% 54.99/7.51      ( r1_tarski(sK9,k2_zfmisc_1(k1_relat_1(sK9),u1_struct_0(sK7))) != iProver_top ),
% 54.99/7.51      inference(light_normalisation,[status(thm)],[c_139126,c_65459]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_139133,plain,
% 54.99/7.51      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(k1_relat_1(sK9),k1_xboole_0)) != iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_15126,c_139130]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_139134,plain,
% 54.99/7.51      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 54.99/7.51      | r1_tarski(sK9,k1_xboole_0) != iProver_top ),
% 54.99/7.51      inference(demodulation,[status(thm)],[c_139133,c_12]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5109,plain,
% 54.99/7.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 54.99/7.51      | r1_tarski(X0,X1) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_6293,plain,
% 54.99/7.51      ( r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))) = iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5128,c_5109]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_15203,plain,
% 54.99/7.51      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),k1_xboole_0)) = iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_15126,c_6293]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_15213,plain,
% 54.99/7.51      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 54.99/7.51      | r1_tarski(sK9,k1_xboole_0) = iProver_top ),
% 54.99/7.51      inference(demodulation,[status(thm)],[c_15203,c_12]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_139350,plain,
% 54.99/7.51      ( u1_struct_0(sK6) = k1_relat_1(sK9) ),
% 54.99/7.51      inference(global_propositional_subsumption,
% 54.99/7.51                [status(thm)],
% 54.99/7.51                [c_139134,c_15213]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_139575,plain,
% 54.99/7.51      ( v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 54.99/7.51      | r1_tarski(sK9,k2_zfmisc_1(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) != iProver_top ),
% 54.99/7.51      inference(demodulation,[status(thm)],[c_139350,c_36557]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_5070,plain,
% 54.99/7.51      ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 54.99/7.51      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_65551,plain,
% 54.99/7.51      ( v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 54.99/7.51      inference(demodulation,[status(thm)],[c_65459,c_5070]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_6292,plain,
% 54.99/7.51      ( r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) = iProver_top ),
% 54.99/7.51      inference(superposition,[status(thm)],[c_5071,c_5109]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(c_65548,plain,
% 54.99/7.51      ( r1_tarski(sK9,k2_zfmisc_1(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) = iProver_top ),
% 54.99/7.51      inference(demodulation,[status(thm)],[c_65459,c_6292]) ).
% 54.99/7.51  
% 54.99/7.51  cnf(contradiction,plain,
% 54.99/7.51      ( $false ),
% 54.99/7.51      inference(minisat,[status(thm)],[c_139575,c_65551,c_65548]) ).
% 54.99/7.51  
% 54.99/7.51  
% 54.99/7.51  % SZS output end CNFRefutation for theBenchmark.p
% 54.99/7.51  
% 54.99/7.51  ------                               Statistics
% 54.99/7.51  
% 54.99/7.51  ------ General
% 54.99/7.51  
% 54.99/7.51  abstr_ref_over_cycles:                  0
% 54.99/7.51  abstr_ref_under_cycles:                 0
% 54.99/7.51  gc_basic_clause_elim:                   0
% 54.99/7.51  forced_gc_time:                         0
% 54.99/7.51  parsing_time:                           0.014
% 54.99/7.51  unif_index_cands_time:                  0.
% 54.99/7.51  unif_index_add_time:                    0.
% 54.99/7.51  orderings_time:                         0.
% 54.99/7.51  out_proof_time:                         0.064
% 54.99/7.51  total_time:                             6.718
% 54.99/7.51  num_of_symbols:                         64
% 54.99/7.51  num_of_terms:                           108722
% 54.99/7.51  
% 54.99/7.51  ------ Preprocessing
% 54.99/7.51  
% 54.99/7.51  num_of_splits:                          0
% 54.99/7.51  num_of_split_atoms:                     0
% 54.99/7.51  num_of_reused_defs:                     0
% 54.99/7.51  num_eq_ax_congr_red:                    54
% 54.99/7.51  num_of_sem_filtered_clauses:            1
% 54.99/7.51  num_of_subtypes:                        0
% 54.99/7.51  monotx_restored_types:                  0
% 54.99/7.51  sat_num_of_epr_types:                   0
% 54.99/7.51  sat_num_of_non_cyclic_types:            0
% 54.99/7.51  sat_guarded_non_collapsed_types:        0
% 54.99/7.51  num_pure_diseq_elim:                    0
% 54.99/7.51  simp_replaced_by:                       0
% 54.99/7.51  res_preprocessed:                       321
% 54.99/7.51  prep_upred:                             0
% 54.99/7.51  prep_unflattend:                        48
% 54.99/7.51  smt_new_axioms:                         0
% 54.99/7.51  pred_elim_cands:                        11
% 54.99/7.51  pred_elim:                              0
% 54.99/7.51  pred_elim_cl:                           0
% 54.99/7.51  pred_elim_cycles:                       6
% 54.99/7.51  merged_defs:                            16
% 54.99/7.51  merged_defs_ncl:                        0
% 54.99/7.51  bin_hyper_res:                          17
% 54.99/7.51  prep_cycles:                            4
% 54.99/7.51  pred_elim_time:                         0.05
% 54.99/7.51  splitting_time:                         0.
% 54.99/7.51  sem_filter_time:                        0.
% 54.99/7.51  monotx_time:                            0.001
% 54.99/7.51  subtype_inf_time:                       0.
% 54.99/7.51  
% 54.99/7.51  ------ Problem properties
% 54.99/7.51  
% 54.99/7.51  clauses:                                70
% 54.99/7.51  conjectures:                            13
% 54.99/7.51  epr:                                    19
% 54.99/7.51  horn:                                   53
% 54.99/7.51  ground:                                 14
% 54.99/7.51  unary:                                  17
% 54.99/7.51  binary:                                 19
% 54.99/7.51  lits:                                   210
% 54.99/7.51  lits_eq:                                26
% 54.99/7.51  fd_pure:                                0
% 54.99/7.51  fd_pseudo:                              0
% 54.99/7.51  fd_cond:                                6
% 54.99/7.51  fd_pseudo_cond:                         4
% 54.99/7.51  ac_symbols:                             0
% 54.99/7.51  
% 54.99/7.51  ------ Propositional Solver
% 54.99/7.51  
% 54.99/7.51  prop_solver_calls:                      60
% 54.99/7.51  prop_fast_solver_calls:                 9794
% 54.99/7.51  smt_solver_calls:                       0
% 54.99/7.51  smt_fast_solver_calls:                  0
% 54.99/7.51  prop_num_of_clauses:                    59752
% 54.99/7.51  prop_preprocess_simplified:             86158
% 54.99/7.51  prop_fo_subsumed:                       630
% 54.99/7.51  prop_solver_time:                       0.
% 54.99/7.51  smt_solver_time:                        0.
% 54.99/7.51  smt_fast_solver_time:                   0.
% 54.99/7.51  prop_fast_solver_time:                  0.
% 54.99/7.51  prop_unsat_core_time:                   0.005
% 54.99/7.51  
% 54.99/7.51  ------ QBF
% 54.99/7.51  
% 54.99/7.51  qbf_q_res:                              0
% 54.99/7.51  qbf_num_tautologies:                    0
% 54.99/7.51  qbf_prep_cycles:                        0
% 54.99/7.51  
% 54.99/7.51  ------ BMC1
% 54.99/7.51  
% 54.99/7.51  bmc1_current_bound:                     -1
% 54.99/7.51  bmc1_last_solved_bound:                 -1
% 54.99/7.51  bmc1_unsat_core_size:                   -1
% 54.99/7.51  bmc1_unsat_core_parents_size:           -1
% 54.99/7.51  bmc1_merge_next_fun:                    0
% 54.99/7.51  bmc1_unsat_core_clauses_time:           0.
% 54.99/7.51  
% 54.99/7.51  ------ Instantiation
% 54.99/7.51  
% 54.99/7.51  inst_num_of_clauses:                    6320
% 54.99/7.51  inst_num_in_passive:                    1925
% 54.99/7.51  inst_num_in_active:                     4356
% 54.99/7.51  inst_num_in_unprocessed:                2073
% 54.99/7.51  inst_num_of_loops:                      6249
% 54.99/7.51  inst_num_of_learning_restarts:          1
% 54.99/7.51  inst_num_moves_active_passive:          1887
% 54.99/7.51  inst_lit_activity:                      0
% 54.99/7.51  inst_lit_activity_moves:                0
% 54.99/7.51  inst_num_tautologies:                   0
% 54.99/7.51  inst_num_prop_implied:                  0
% 54.99/7.51  inst_num_existing_simplified:           0
% 54.99/7.51  inst_num_eq_res_simplified:             0
% 54.99/7.51  inst_num_child_elim:                    0
% 54.99/7.51  inst_num_of_dismatching_blockings:      12159
% 54.99/7.51  inst_num_of_non_proper_insts:           16075
% 54.99/7.51  inst_num_of_duplicates:                 0
% 54.99/7.51  inst_inst_num_from_inst_to_res:         0
% 54.99/7.51  inst_dismatching_checking_time:         0.
% 54.99/7.51  
% 54.99/7.51  ------ Resolution
% 54.99/7.51  
% 54.99/7.51  res_num_of_clauses:                     90
% 54.99/7.51  res_num_in_passive:                     90
% 54.99/7.51  res_num_in_active:                      0
% 54.99/7.51  res_num_of_loops:                       325
% 54.99/7.51  res_forward_subset_subsumed:            472
% 54.99/7.51  res_backward_subset_subsumed:           52
% 54.99/7.51  res_forward_subsumed:                   0
% 54.99/7.51  res_backward_subsumed:                  0
% 54.99/7.51  res_forward_subsumption_resolution:     0
% 54.99/7.51  res_backward_subsumption_resolution:    0
% 54.99/7.51  res_clause_to_clause_subsumption:       83764
% 54.99/7.51  res_orphan_elimination:                 0
% 54.99/7.51  res_tautology_del:                      764
% 54.99/7.51  res_num_eq_res_simplified:              0
% 54.99/7.51  res_num_sel_changes:                    0
% 54.99/7.51  res_moves_from_active_to_pass:          0
% 54.99/7.51  
% 54.99/7.51  ------ Superposition
% 54.99/7.51  
% 54.99/7.51  sup_time_total:                         0.
% 54.99/7.51  sup_time_generating:                    0.
% 54.99/7.51  sup_time_sim_full:                      0.
% 54.99/7.51  sup_time_sim_immed:                     0.
% 54.99/7.51  
% 54.99/7.51  sup_num_of_clauses:                     6127
% 54.99/7.51  sup_num_in_active:                      384
% 54.99/7.51  sup_num_in_passive:                     5743
% 54.99/7.51  sup_num_of_loops:                       1248
% 54.99/7.51  sup_fw_superposition:                   7544
% 54.99/7.51  sup_bw_superposition:                   5816
% 54.99/7.51  sup_immediate_simplified:               3895
% 54.99/7.51  sup_given_eliminated:                   3
% 54.99/7.51  comparisons_done:                       0
% 54.99/7.51  comparisons_avoided:                    1004
% 54.99/7.51  
% 54.99/7.51  ------ Simplifications
% 54.99/7.51  
% 54.99/7.51  
% 54.99/7.51  sim_fw_subset_subsumed:                 1658
% 54.99/7.51  sim_bw_subset_subsumed:                 1942
% 54.99/7.51  sim_fw_subsumed:                        1336
% 54.99/7.51  sim_bw_subsumed:                        414
% 54.99/7.51  sim_fw_subsumption_res:                 0
% 54.99/7.51  sim_bw_subsumption_res:                 0
% 54.99/7.51  sim_tautology_del:                      197
% 54.99/7.51  sim_eq_tautology_del:                   259
% 54.99/7.51  sim_eq_res_simp:                        0
% 54.99/7.51  sim_fw_demodulated:                     751
% 54.99/7.51  sim_bw_demodulated:                     336
% 54.99/7.51  sim_light_normalised:                   231
% 54.99/7.51  sim_joinable_taut:                      0
% 54.99/7.51  sim_joinable_simp:                      0
% 54.99/7.51  sim_ac_normalised:                      0
% 54.99/7.51  sim_smt_subsumption:                    0
% 54.99/7.51  
%------------------------------------------------------------------------------
