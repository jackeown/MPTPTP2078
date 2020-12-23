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
% DateTime   : Thu Dec  3 12:11:47 EST 2020

% Result     : Theorem 11.47s
% Output     : CNFRefutation 11.47s
% Verified   : 
% Statistics : Number of formulae       :  188 (2512 expanded)
%              Number of clauses        :  125 ( 758 expanded)
%              Number of leaves         :   13 ( 669 expanded)
%              Depth                    :   26
%              Number of atoms          : 1007 (23279 expanded)
%              Number of equality atoms :  441 (2926 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f35,plain,(
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
     => ( ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK4 = X2
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
              | ~ v5_pre_topc(sK3,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK3,X0,X1) )
            & sK3 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
                  | ~ v5_pre_topc(X2,X0,sK2) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
                  | v5_pre_topc(X2,X0,sK2) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK1,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK1,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ v5_pre_topc(sK3,sK1,sK2) )
    & ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | v5_pre_topc(sK3,sK1,sK2) )
    & sK3 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f35,f34,f33,f32])).

fof(f64,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f36])).

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

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f37,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

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

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f38,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
    inference(cnf_transformation,[],[f36])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,
    ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
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
    inference(equality_resolution,[],[f52])).

fof(f53,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
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
    inference(equality_resolution,[],[f51])).

cnf(c_17,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1526,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( sK3 = sK4 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1547,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1526,c_18])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1530,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1519,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1536,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1538,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1884,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1536,c_1538])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1543,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2145,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1884,c_1543])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1537,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1879,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1536,c_1537])).

cnf(c_2562,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2145,c_1879])).

cnf(c_2563,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2562])).

cnf(c_2568,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(superposition,[status(thm)],[c_1519,c_2563])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1534,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2576,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2568,c_1534])).

cnf(c_3277,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2)
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2576])).

cnf(c_32,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1672,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1673,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1672])).

cnf(c_4004,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3277,c_32,c_1673])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1539,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | v4_pre_topc(X3,X2) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4039,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | v4_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4004,c_1539])).

cnf(c_4090,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v4_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4039,c_4004])).

cnf(c_1638,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1639,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1638])).

cnf(c_8913,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),X1) = iProver_top
    | v4_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4090,c_32,c_1639,c_1673])).

cnf(c_8914,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v4_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_8913])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1542,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8921,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v5_pre_topc(X0,X1,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v4_pre_topc(sK0(X1,sK2,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8914,c_1542])).

cnf(c_9188,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v4_pre_topc(sK0(X1,sK2,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(sK0(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | v5_pre_topc(X0,X1,sK2) = iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8921,c_32])).

cnf(c_9189,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v5_pre_topc(X0,X1,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v4_pre_topc(sK0(X1,sK2,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9188])).

cnf(c_9194,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v5_pre_topc(X0,X1,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v4_pre_topc(sK0(X1,sK2,X0),sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_9189])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_31,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9305,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v5_pre_topc(X0,X1,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v4_pre_topc(sK0(X1,sK2,X0),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9194,c_31,c_32])).

cnf(c_9306,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v5_pre_topc(X0,X1,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v4_pre_topc(sK0(X1,sK2,X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9305])).

cnf(c_9312,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_9306])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1517,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2569,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(superposition,[status(thm)],[c_1517,c_2563])).

cnf(c_2649,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2569,c_1534])).

cnf(c_3375,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1)
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2649])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_63,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_65,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_4905,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3375,c_30,c_65])).

cnf(c_9318,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9312,c_4905])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1525,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1540,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2931,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_1540])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_36,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_37,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1760,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1761,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1760])).

cnf(c_3222,plain,
    ( m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2931,c_30,c_32,c_36,c_37,c_65,c_1639,c_1673,c_1761])).

cnf(c_3223,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3222])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1532,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | v4_pre_topc(X0,X1) = iProver_top
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3227,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3223,c_1532])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v4_pre_topc(sK0(X1,X2,X0),X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1541,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v4_pre_topc(sK0(X1,X2,X0),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2926,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_1541])).

cnf(c_3217,plain,
    ( v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2926,c_30,c_32,c_36,c_37,c_65,c_1639,c_1673,c_1761])).

cnf(c_3218,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3217])).

cnf(c_3710,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3227,c_31,c_32,c_3218])).

cnf(c_4038,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4004,c_1542])).

cnf(c_4091,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4038,c_4004])).

cnf(c_7472,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4091,c_32,c_1639,c_1673])).

cnf(c_7473,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7472])).

cnf(c_7478,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v5_pre_topc(X0,X1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v4_pre_topc(sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_7473])).

cnf(c_4040,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4004,c_1540])).

cnf(c_4089,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4040,c_4004])).

cnf(c_7661,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v4_pre_topc(sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK2) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v5_pre_topc(X0,X1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7478,c_32,c_1639,c_1673,c_4089])).

cnf(c_7662,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v5_pre_topc(X0,X1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | v4_pre_topc(sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7661])).

cnf(c_7667,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3710,c_7662])).

cnf(c_7668,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7667,c_4905])).

cnf(c_16,negated_conjecture,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1527,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1548,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1527,c_18])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1522,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1546,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1522,c_18])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1521,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1545,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1521,c_18])).

cnf(c_4017,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4004,c_1525])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1529,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4249,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4017,c_1529])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_29,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2865,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2))
    | v5_pre_topc(sK4,X0,sK2)
    | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2881,plain,
    ( v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,X0,sK2) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2865])).

cnf(c_2883,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2881])).

cnf(c_1524,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4018,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4004,c_1524])).

cnf(c_4719,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4249,c_29,c_30,c_31,c_32,c_36,c_1546,c_1545,c_2883,c_4017,c_4018])).

cnf(c_7890,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7668,c_30,c_36,c_65,c_1548,c_1546,c_1545,c_1761,c_4719])).

cnf(c_4247,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4017,c_1540])).

cnf(c_4822,plain,
    ( m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4247,c_30,c_32,c_36,c_65,c_1761,c_4018])).

cnf(c_4823,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4822])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1528,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4250,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4017,c_1528])).

cnf(c_4811,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4250,c_29,c_30,c_31,c_32,c_36,c_1546,c_1545,c_4018])).

cnf(c_4248,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4017,c_1541])).

cnf(c_4714,plain,
    ( v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4248,c_30,c_32,c_36,c_65,c_1761,c_4018])).

cnf(c_4715,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_4714])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9318,c_7890,c_4823,c_4811,c_4715,c_1761,c_1545,c_1546,c_65,c_36,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:31:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 11.47/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.47/2.00  
% 11.47/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.47/2.00  
% 11.47/2.00  ------  iProver source info
% 11.47/2.00  
% 11.47/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.47/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.47/2.00  git: non_committed_changes: false
% 11.47/2.00  git: last_make_outside_of_git: false
% 11.47/2.00  
% 11.47/2.00  ------ 
% 11.47/2.00  
% 11.47/2.00  ------ Input Options
% 11.47/2.00  
% 11.47/2.00  --out_options                           all
% 11.47/2.00  --tptp_safe_out                         true
% 11.47/2.00  --problem_path                          ""
% 11.47/2.00  --include_path                          ""
% 11.47/2.00  --clausifier                            res/vclausify_rel
% 11.47/2.00  --clausifier_options                    ""
% 11.47/2.00  --stdin                                 false
% 11.47/2.00  --stats_out                             all
% 11.47/2.00  
% 11.47/2.00  ------ General Options
% 11.47/2.00  
% 11.47/2.00  --fof                                   false
% 11.47/2.00  --time_out_real                         305.
% 11.47/2.00  --time_out_virtual                      -1.
% 11.47/2.00  --symbol_type_check                     false
% 11.47/2.00  --clausify_out                          false
% 11.47/2.00  --sig_cnt_out                           false
% 11.47/2.00  --trig_cnt_out                          false
% 11.47/2.00  --trig_cnt_out_tolerance                1.
% 11.47/2.00  --trig_cnt_out_sk_spl                   false
% 11.47/2.00  --abstr_cl_out                          false
% 11.47/2.00  
% 11.47/2.00  ------ Global Options
% 11.47/2.00  
% 11.47/2.00  --schedule                              default
% 11.47/2.00  --add_important_lit                     false
% 11.47/2.00  --prop_solver_per_cl                    1000
% 11.47/2.00  --min_unsat_core                        false
% 11.47/2.00  --soft_assumptions                      false
% 11.47/2.00  --soft_lemma_size                       3
% 11.47/2.00  --prop_impl_unit_size                   0
% 11.47/2.00  --prop_impl_unit                        []
% 11.47/2.00  --share_sel_clauses                     true
% 11.47/2.00  --reset_solvers                         false
% 11.47/2.00  --bc_imp_inh                            [conj_cone]
% 11.47/2.00  --conj_cone_tolerance                   3.
% 11.47/2.00  --extra_neg_conj                        none
% 11.47/2.00  --large_theory_mode                     true
% 11.47/2.00  --prolific_symb_bound                   200
% 11.47/2.00  --lt_threshold                          2000
% 11.47/2.00  --clause_weak_htbl                      true
% 11.47/2.00  --gc_record_bc_elim                     false
% 11.47/2.00  
% 11.47/2.00  ------ Preprocessing Options
% 11.47/2.00  
% 11.47/2.00  --preprocessing_flag                    true
% 11.47/2.00  --time_out_prep_mult                    0.1
% 11.47/2.00  --splitting_mode                        input
% 11.47/2.00  --splitting_grd                         true
% 11.47/2.00  --splitting_cvd                         false
% 11.47/2.00  --splitting_cvd_svl                     false
% 11.47/2.00  --splitting_nvd                         32
% 11.47/2.00  --sub_typing                            true
% 11.47/2.00  --prep_gs_sim                           true
% 11.47/2.00  --prep_unflatten                        true
% 11.47/2.00  --prep_res_sim                          true
% 11.47/2.00  --prep_upred                            true
% 11.47/2.00  --prep_sem_filter                       exhaustive
% 11.47/2.00  --prep_sem_filter_out                   false
% 11.47/2.00  --pred_elim                             true
% 11.47/2.00  --res_sim_input                         true
% 11.47/2.00  --eq_ax_congr_red                       true
% 11.47/2.00  --pure_diseq_elim                       true
% 11.47/2.00  --brand_transform                       false
% 11.47/2.00  --non_eq_to_eq                          false
% 11.47/2.00  --prep_def_merge                        true
% 11.47/2.00  --prep_def_merge_prop_impl              false
% 11.47/2.00  --prep_def_merge_mbd                    true
% 11.47/2.00  --prep_def_merge_tr_red                 false
% 11.47/2.00  --prep_def_merge_tr_cl                  false
% 11.47/2.00  --smt_preprocessing                     true
% 11.47/2.00  --smt_ac_axioms                         fast
% 11.47/2.00  --preprocessed_out                      false
% 11.47/2.00  --preprocessed_stats                    false
% 11.47/2.00  
% 11.47/2.00  ------ Abstraction refinement Options
% 11.47/2.00  
% 11.47/2.00  --abstr_ref                             []
% 11.47/2.00  --abstr_ref_prep                        false
% 11.47/2.00  --abstr_ref_until_sat                   false
% 11.47/2.00  --abstr_ref_sig_restrict                funpre
% 11.47/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.47/2.00  --abstr_ref_under                       []
% 11.47/2.00  
% 11.47/2.00  ------ SAT Options
% 11.47/2.00  
% 11.47/2.00  --sat_mode                              false
% 11.47/2.00  --sat_fm_restart_options                ""
% 11.47/2.00  --sat_gr_def                            false
% 11.47/2.00  --sat_epr_types                         true
% 11.47/2.00  --sat_non_cyclic_types                  false
% 11.47/2.00  --sat_finite_models                     false
% 11.47/2.00  --sat_fm_lemmas                         false
% 11.47/2.00  --sat_fm_prep                           false
% 11.47/2.00  --sat_fm_uc_incr                        true
% 11.47/2.00  --sat_out_model                         small
% 11.47/2.00  --sat_out_clauses                       false
% 11.47/2.00  
% 11.47/2.00  ------ QBF Options
% 11.47/2.00  
% 11.47/2.00  --qbf_mode                              false
% 11.47/2.00  --qbf_elim_univ                         false
% 11.47/2.00  --qbf_dom_inst                          none
% 11.47/2.00  --qbf_dom_pre_inst                      false
% 11.47/2.00  --qbf_sk_in                             false
% 11.47/2.00  --qbf_pred_elim                         true
% 11.47/2.00  --qbf_split                             512
% 11.47/2.00  
% 11.47/2.00  ------ BMC1 Options
% 11.47/2.00  
% 11.47/2.00  --bmc1_incremental                      false
% 11.47/2.00  --bmc1_axioms                           reachable_all
% 11.47/2.00  --bmc1_min_bound                        0
% 11.47/2.00  --bmc1_max_bound                        -1
% 11.47/2.00  --bmc1_max_bound_default                -1
% 11.47/2.00  --bmc1_symbol_reachability              true
% 11.47/2.00  --bmc1_property_lemmas                  false
% 11.47/2.00  --bmc1_k_induction                      false
% 11.47/2.00  --bmc1_non_equiv_states                 false
% 11.47/2.00  --bmc1_deadlock                         false
% 11.47/2.00  --bmc1_ucm                              false
% 11.47/2.00  --bmc1_add_unsat_core                   none
% 11.47/2.00  --bmc1_unsat_core_children              false
% 11.47/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.47/2.00  --bmc1_out_stat                         full
% 11.47/2.00  --bmc1_ground_init                      false
% 11.47/2.00  --bmc1_pre_inst_next_state              false
% 11.47/2.00  --bmc1_pre_inst_state                   false
% 11.47/2.00  --bmc1_pre_inst_reach_state             false
% 11.47/2.00  --bmc1_out_unsat_core                   false
% 11.47/2.00  --bmc1_aig_witness_out                  false
% 11.47/2.00  --bmc1_verbose                          false
% 11.47/2.00  --bmc1_dump_clauses_tptp                false
% 11.47/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.47/2.00  --bmc1_dump_file                        -
% 11.47/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.47/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.47/2.00  --bmc1_ucm_extend_mode                  1
% 11.47/2.00  --bmc1_ucm_init_mode                    2
% 11.47/2.00  --bmc1_ucm_cone_mode                    none
% 11.47/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.47/2.00  --bmc1_ucm_relax_model                  4
% 11.47/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.47/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.47/2.00  --bmc1_ucm_layered_model                none
% 11.47/2.00  --bmc1_ucm_max_lemma_size               10
% 11.47/2.00  
% 11.47/2.00  ------ AIG Options
% 11.47/2.00  
% 11.47/2.00  --aig_mode                              false
% 11.47/2.00  
% 11.47/2.00  ------ Instantiation Options
% 11.47/2.00  
% 11.47/2.00  --instantiation_flag                    true
% 11.47/2.00  --inst_sos_flag                         true
% 11.47/2.00  --inst_sos_phase                        true
% 11.47/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.47/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.47/2.00  --inst_lit_sel_side                     num_symb
% 11.47/2.00  --inst_solver_per_active                1400
% 11.47/2.00  --inst_solver_calls_frac                1.
% 11.47/2.00  --inst_passive_queue_type               priority_queues
% 11.47/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.47/2.00  --inst_passive_queues_freq              [25;2]
% 11.47/2.00  --inst_dismatching                      true
% 11.47/2.00  --inst_eager_unprocessed_to_passive     true
% 11.47/2.00  --inst_prop_sim_given                   true
% 11.47/2.00  --inst_prop_sim_new                     false
% 11.47/2.00  --inst_subs_new                         false
% 11.47/2.00  --inst_eq_res_simp                      false
% 11.47/2.00  --inst_subs_given                       false
% 11.47/2.00  --inst_orphan_elimination               true
% 11.47/2.00  --inst_learning_loop_flag               true
% 11.47/2.00  --inst_learning_start                   3000
% 11.47/2.00  --inst_learning_factor                  2
% 11.47/2.00  --inst_start_prop_sim_after_learn       3
% 11.47/2.00  --inst_sel_renew                        solver
% 11.47/2.00  --inst_lit_activity_flag                true
% 11.47/2.00  --inst_restr_to_given                   false
% 11.47/2.00  --inst_activity_threshold               500
% 11.47/2.00  --inst_out_proof                        true
% 11.47/2.00  
% 11.47/2.00  ------ Resolution Options
% 11.47/2.00  
% 11.47/2.00  --resolution_flag                       true
% 11.47/2.00  --res_lit_sel                           adaptive
% 11.47/2.00  --res_lit_sel_side                      none
% 11.47/2.00  --res_ordering                          kbo
% 11.47/2.00  --res_to_prop_solver                    active
% 11.47/2.00  --res_prop_simpl_new                    false
% 11.47/2.00  --res_prop_simpl_given                  true
% 11.47/2.00  --res_passive_queue_type                priority_queues
% 11.47/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.47/2.00  --res_passive_queues_freq               [15;5]
% 11.47/2.00  --res_forward_subs                      full
% 11.47/2.00  --res_backward_subs                     full
% 11.47/2.00  --res_forward_subs_resolution           true
% 11.47/2.00  --res_backward_subs_resolution          true
% 11.47/2.00  --res_orphan_elimination                true
% 11.47/2.00  --res_time_limit                        2.
% 11.47/2.00  --res_out_proof                         true
% 11.47/2.00  
% 11.47/2.00  ------ Superposition Options
% 11.47/2.00  
% 11.47/2.00  --superposition_flag                    true
% 11.47/2.00  --sup_passive_queue_type                priority_queues
% 11.47/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.47/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.47/2.00  --demod_completeness_check              fast
% 11.47/2.00  --demod_use_ground                      true
% 11.47/2.00  --sup_to_prop_solver                    passive
% 11.47/2.00  --sup_prop_simpl_new                    true
% 11.47/2.00  --sup_prop_simpl_given                  true
% 11.47/2.00  --sup_fun_splitting                     true
% 11.47/2.00  --sup_smt_interval                      50000
% 11.47/2.00  
% 11.47/2.00  ------ Superposition Simplification Setup
% 11.47/2.00  
% 11.47/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.47/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.47/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.47/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.47/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.47/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.47/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.47/2.00  --sup_immed_triv                        [TrivRules]
% 11.47/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.47/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.47/2.00  --sup_immed_bw_main                     []
% 11.47/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.47/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.47/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.47/2.00  --sup_input_bw                          []
% 11.47/2.00  
% 11.47/2.00  ------ Combination Options
% 11.47/2.00  
% 11.47/2.00  --comb_res_mult                         3
% 11.47/2.00  --comb_sup_mult                         2
% 11.47/2.00  --comb_inst_mult                        10
% 11.47/2.00  
% 11.47/2.00  ------ Debug Options
% 11.47/2.00  
% 11.47/2.00  --dbg_backtrace                         false
% 11.47/2.00  --dbg_dump_prop_clauses                 false
% 11.47/2.00  --dbg_dump_prop_clauses_file            -
% 11.47/2.00  --dbg_out_stat                          false
% 11.47/2.00  ------ Parsing...
% 11.47/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.47/2.00  
% 11.47/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.47/2.00  
% 11.47/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.47/2.00  
% 11.47/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.47/2.00  ------ Proving...
% 11.47/2.00  ------ Problem Properties 
% 11.47/2.00  
% 11.47/2.00  
% 11.47/2.00  clauses                                 29
% 11.47/2.00  conjectures                             13
% 11.47/2.00  EPR                                     7
% 11.47/2.00  Horn                                    26
% 11.47/2.00  unary                                   11
% 11.47/2.00  binary                                  5
% 11.47/2.00  lits                                    102
% 11.47/2.00  lits eq                                 6
% 11.47/2.00  fd_pure                                 0
% 11.47/2.00  fd_pseudo                               0
% 11.47/2.00  fd_cond                                 0
% 11.47/2.00  fd_pseudo_cond                          2
% 11.47/2.00  AC symbols                              0
% 11.47/2.00  
% 11.47/2.00  ------ Schedule dynamic 5 is on 
% 11.47/2.00  
% 11.47/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.47/2.00  
% 11.47/2.00  
% 11.47/2.00  ------ 
% 11.47/2.00  Current options:
% 11.47/2.00  ------ 
% 11.47/2.00  
% 11.47/2.00  ------ Input Options
% 11.47/2.00  
% 11.47/2.00  --out_options                           all
% 11.47/2.00  --tptp_safe_out                         true
% 11.47/2.00  --problem_path                          ""
% 11.47/2.00  --include_path                          ""
% 11.47/2.00  --clausifier                            res/vclausify_rel
% 11.47/2.00  --clausifier_options                    ""
% 11.47/2.00  --stdin                                 false
% 11.47/2.00  --stats_out                             all
% 11.47/2.00  
% 11.47/2.00  ------ General Options
% 11.47/2.00  
% 11.47/2.00  --fof                                   false
% 11.47/2.00  --time_out_real                         305.
% 11.47/2.00  --time_out_virtual                      -1.
% 11.47/2.00  --symbol_type_check                     false
% 11.47/2.00  --clausify_out                          false
% 11.47/2.00  --sig_cnt_out                           false
% 11.47/2.00  --trig_cnt_out                          false
% 11.47/2.00  --trig_cnt_out_tolerance                1.
% 11.47/2.00  --trig_cnt_out_sk_spl                   false
% 11.47/2.00  --abstr_cl_out                          false
% 11.47/2.00  
% 11.47/2.00  ------ Global Options
% 11.47/2.00  
% 11.47/2.00  --schedule                              default
% 11.47/2.00  --add_important_lit                     false
% 11.47/2.00  --prop_solver_per_cl                    1000
% 11.47/2.00  --min_unsat_core                        false
% 11.47/2.00  --soft_assumptions                      false
% 11.47/2.00  --soft_lemma_size                       3
% 11.47/2.00  --prop_impl_unit_size                   0
% 11.47/2.00  --prop_impl_unit                        []
% 11.47/2.00  --share_sel_clauses                     true
% 11.47/2.00  --reset_solvers                         false
% 11.47/2.00  --bc_imp_inh                            [conj_cone]
% 11.47/2.00  --conj_cone_tolerance                   3.
% 11.47/2.00  --extra_neg_conj                        none
% 11.47/2.00  --large_theory_mode                     true
% 11.47/2.00  --prolific_symb_bound                   200
% 11.47/2.00  --lt_threshold                          2000
% 11.47/2.00  --clause_weak_htbl                      true
% 11.47/2.00  --gc_record_bc_elim                     false
% 11.47/2.00  
% 11.47/2.00  ------ Preprocessing Options
% 11.47/2.00  
% 11.47/2.00  --preprocessing_flag                    true
% 11.47/2.00  --time_out_prep_mult                    0.1
% 11.47/2.00  --splitting_mode                        input
% 11.47/2.00  --splitting_grd                         true
% 11.47/2.00  --splitting_cvd                         false
% 11.47/2.00  --splitting_cvd_svl                     false
% 11.47/2.00  --splitting_nvd                         32
% 11.47/2.00  --sub_typing                            true
% 11.47/2.00  --prep_gs_sim                           true
% 11.47/2.00  --prep_unflatten                        true
% 11.47/2.00  --prep_res_sim                          true
% 11.47/2.00  --prep_upred                            true
% 11.47/2.00  --prep_sem_filter                       exhaustive
% 11.47/2.00  --prep_sem_filter_out                   false
% 11.47/2.00  --pred_elim                             true
% 11.47/2.00  --res_sim_input                         true
% 11.47/2.00  --eq_ax_congr_red                       true
% 11.47/2.00  --pure_diseq_elim                       true
% 11.47/2.00  --brand_transform                       false
% 11.47/2.00  --non_eq_to_eq                          false
% 11.47/2.00  --prep_def_merge                        true
% 11.47/2.00  --prep_def_merge_prop_impl              false
% 11.47/2.00  --prep_def_merge_mbd                    true
% 11.47/2.00  --prep_def_merge_tr_red                 false
% 11.47/2.00  --prep_def_merge_tr_cl                  false
% 11.47/2.00  --smt_preprocessing                     true
% 11.47/2.00  --smt_ac_axioms                         fast
% 11.47/2.00  --preprocessed_out                      false
% 11.47/2.00  --preprocessed_stats                    false
% 11.47/2.00  
% 11.47/2.00  ------ Abstraction refinement Options
% 11.47/2.00  
% 11.47/2.00  --abstr_ref                             []
% 11.47/2.00  --abstr_ref_prep                        false
% 11.47/2.00  --abstr_ref_until_sat                   false
% 11.47/2.00  --abstr_ref_sig_restrict                funpre
% 11.47/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.47/2.00  --abstr_ref_under                       []
% 11.47/2.00  
% 11.47/2.00  ------ SAT Options
% 11.47/2.00  
% 11.47/2.00  --sat_mode                              false
% 11.47/2.00  --sat_fm_restart_options                ""
% 11.47/2.00  --sat_gr_def                            false
% 11.47/2.00  --sat_epr_types                         true
% 11.47/2.00  --sat_non_cyclic_types                  false
% 11.47/2.00  --sat_finite_models                     false
% 11.47/2.00  --sat_fm_lemmas                         false
% 11.47/2.00  --sat_fm_prep                           false
% 11.47/2.00  --sat_fm_uc_incr                        true
% 11.47/2.00  --sat_out_model                         small
% 11.47/2.00  --sat_out_clauses                       false
% 11.47/2.00  
% 11.47/2.00  ------ QBF Options
% 11.47/2.00  
% 11.47/2.00  --qbf_mode                              false
% 11.47/2.00  --qbf_elim_univ                         false
% 11.47/2.00  --qbf_dom_inst                          none
% 11.47/2.00  --qbf_dom_pre_inst                      false
% 11.47/2.00  --qbf_sk_in                             false
% 11.47/2.00  --qbf_pred_elim                         true
% 11.47/2.00  --qbf_split                             512
% 11.47/2.00  
% 11.47/2.00  ------ BMC1 Options
% 11.47/2.00  
% 11.47/2.00  --bmc1_incremental                      false
% 11.47/2.00  --bmc1_axioms                           reachable_all
% 11.47/2.00  --bmc1_min_bound                        0
% 11.47/2.00  --bmc1_max_bound                        -1
% 11.47/2.00  --bmc1_max_bound_default                -1
% 11.47/2.00  --bmc1_symbol_reachability              true
% 11.47/2.00  --bmc1_property_lemmas                  false
% 11.47/2.00  --bmc1_k_induction                      false
% 11.47/2.00  --bmc1_non_equiv_states                 false
% 11.47/2.00  --bmc1_deadlock                         false
% 11.47/2.00  --bmc1_ucm                              false
% 11.47/2.00  --bmc1_add_unsat_core                   none
% 11.47/2.00  --bmc1_unsat_core_children              false
% 11.47/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.47/2.00  --bmc1_out_stat                         full
% 11.47/2.00  --bmc1_ground_init                      false
% 11.47/2.00  --bmc1_pre_inst_next_state              false
% 11.47/2.00  --bmc1_pre_inst_state                   false
% 11.47/2.00  --bmc1_pre_inst_reach_state             false
% 11.47/2.00  --bmc1_out_unsat_core                   false
% 11.47/2.00  --bmc1_aig_witness_out                  false
% 11.47/2.00  --bmc1_verbose                          false
% 11.47/2.00  --bmc1_dump_clauses_tptp                false
% 11.47/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.47/2.00  --bmc1_dump_file                        -
% 11.47/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.47/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.47/2.00  --bmc1_ucm_extend_mode                  1
% 11.47/2.00  --bmc1_ucm_init_mode                    2
% 11.47/2.00  --bmc1_ucm_cone_mode                    none
% 11.47/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.47/2.00  --bmc1_ucm_relax_model                  4
% 11.47/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.47/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.47/2.00  --bmc1_ucm_layered_model                none
% 11.47/2.00  --bmc1_ucm_max_lemma_size               10
% 11.47/2.00  
% 11.47/2.00  ------ AIG Options
% 11.47/2.00  
% 11.47/2.00  --aig_mode                              false
% 11.47/2.00  
% 11.47/2.00  ------ Instantiation Options
% 11.47/2.00  
% 11.47/2.00  --instantiation_flag                    true
% 11.47/2.00  --inst_sos_flag                         true
% 11.47/2.00  --inst_sos_phase                        true
% 11.47/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.47/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.47/2.00  --inst_lit_sel_side                     none
% 11.47/2.00  --inst_solver_per_active                1400
% 11.47/2.00  --inst_solver_calls_frac                1.
% 11.47/2.00  --inst_passive_queue_type               priority_queues
% 11.47/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.47/2.00  --inst_passive_queues_freq              [25;2]
% 11.47/2.00  --inst_dismatching                      true
% 11.47/2.00  --inst_eager_unprocessed_to_passive     true
% 11.47/2.00  --inst_prop_sim_given                   true
% 11.47/2.00  --inst_prop_sim_new                     false
% 11.47/2.00  --inst_subs_new                         false
% 11.47/2.00  --inst_eq_res_simp                      false
% 11.47/2.00  --inst_subs_given                       false
% 11.47/2.00  --inst_orphan_elimination               true
% 11.47/2.00  --inst_learning_loop_flag               true
% 11.47/2.00  --inst_learning_start                   3000
% 11.47/2.00  --inst_learning_factor                  2
% 11.47/2.00  --inst_start_prop_sim_after_learn       3
% 11.47/2.00  --inst_sel_renew                        solver
% 11.47/2.00  --inst_lit_activity_flag                true
% 11.47/2.00  --inst_restr_to_given                   false
% 11.47/2.00  --inst_activity_threshold               500
% 11.47/2.00  --inst_out_proof                        true
% 11.47/2.00  
% 11.47/2.00  ------ Resolution Options
% 11.47/2.00  
% 11.47/2.00  --resolution_flag                       false
% 11.47/2.00  --res_lit_sel                           adaptive
% 11.47/2.00  --res_lit_sel_side                      none
% 11.47/2.00  --res_ordering                          kbo
% 11.47/2.00  --res_to_prop_solver                    active
% 11.47/2.00  --res_prop_simpl_new                    false
% 11.47/2.00  --res_prop_simpl_given                  true
% 11.47/2.00  --res_passive_queue_type                priority_queues
% 11.47/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.47/2.00  --res_passive_queues_freq               [15;5]
% 11.47/2.00  --res_forward_subs                      full
% 11.47/2.00  --res_backward_subs                     full
% 11.47/2.00  --res_forward_subs_resolution           true
% 11.47/2.00  --res_backward_subs_resolution          true
% 11.47/2.00  --res_orphan_elimination                true
% 11.47/2.00  --res_time_limit                        2.
% 11.47/2.00  --res_out_proof                         true
% 11.47/2.00  
% 11.47/2.00  ------ Superposition Options
% 11.47/2.00  
% 11.47/2.00  --superposition_flag                    true
% 11.47/2.00  --sup_passive_queue_type                priority_queues
% 11.47/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.47/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.47/2.00  --demod_completeness_check              fast
% 11.47/2.00  --demod_use_ground                      true
% 11.47/2.00  --sup_to_prop_solver                    passive
% 11.47/2.00  --sup_prop_simpl_new                    true
% 11.47/2.00  --sup_prop_simpl_given                  true
% 11.47/2.00  --sup_fun_splitting                     true
% 11.47/2.00  --sup_smt_interval                      50000
% 11.47/2.00  
% 11.47/2.00  ------ Superposition Simplification Setup
% 11.47/2.00  
% 11.47/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.47/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.47/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.47/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.47/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.47/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.47/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.47/2.00  --sup_immed_triv                        [TrivRules]
% 11.47/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.47/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.47/2.00  --sup_immed_bw_main                     []
% 11.47/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.47/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.47/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.47/2.00  --sup_input_bw                          []
% 11.47/2.00  
% 11.47/2.00  ------ Combination Options
% 11.47/2.00  
% 11.47/2.00  --comb_res_mult                         3
% 11.47/2.00  --comb_sup_mult                         2
% 11.47/2.00  --comb_inst_mult                        10
% 11.47/2.00  
% 11.47/2.00  ------ Debug Options
% 11.47/2.00  
% 11.47/2.00  --dbg_backtrace                         false
% 11.47/2.00  --dbg_dump_prop_clauses                 false
% 11.47/2.00  --dbg_dump_prop_clauses_file            -
% 11.47/2.00  --dbg_out_stat                          false
% 11.47/2.00  
% 11.47/2.00  
% 11.47/2.00  
% 11.47/2.00  
% 11.47/2.00  ------ Proving...
% 11.47/2.00  
% 11.47/2.00  
% 11.47/2.00  % SZS status Theorem for theBenchmark.p
% 11.47/2.00  
% 11.47/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.47/2.00  
% 11.47/2.00  fof(f8,conjecture,(
% 11.47/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 11.47/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/2.00  
% 11.47/2.00  fof(f9,negated_conjecture,(
% 11.47/2.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 11.47/2.00    inference(negated_conjecture,[],[f8])).
% 11.47/2.00  
% 11.47/2.00  fof(f21,plain,(
% 11.47/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.47/2.00    inference(ennf_transformation,[],[f9])).
% 11.47/2.00  
% 11.47/2.00  fof(f22,plain,(
% 11.47/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.47/2.00    inference(flattening,[],[f21])).
% 11.47/2.00  
% 11.47/2.00  fof(f30,plain,(
% 11.47/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.47/2.00    inference(nnf_transformation,[],[f22])).
% 11.47/2.00  
% 11.47/2.00  fof(f31,plain,(
% 11.47/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.47/2.00    inference(flattening,[],[f30])).
% 11.47/2.00  
% 11.47/2.00  fof(f35,plain,(
% 11.47/2.00    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK4 = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK4))) )),
% 11.47/2.00    introduced(choice_axiom,[])).
% 11.47/2.00  
% 11.47/2.00  fof(f34,plain,(
% 11.47/2.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK3,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK3,X0,X1)) & sK3 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 11.47/2.00    introduced(choice_axiom,[])).
% 11.47/2.00  
% 11.47/2.00  fof(f33,plain,(
% 11.47/2.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(X2,X0,sK2)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(X2,X0,sK2)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))) )),
% 11.47/2.00    introduced(choice_axiom,[])).
% 11.47/2.00  
% 11.47/2.00  fof(f32,plain,(
% 11.47/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK1,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK1,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 11.47/2.00    introduced(choice_axiom,[])).
% 11.47/2.00  
% 11.47/2.00  fof(f36,plain,(
% 11.47/2.00    ((((~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(sK3,sK1,sK2)) & (v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,sK1,sK2)) & sK3 = sK4 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 11.47/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f35,f34,f33,f32])).
% 11.47/2.00  
% 11.47/2.00  fof(f64,plain,(
% 11.47/2.00    v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,sK1,sK2)),
% 11.47/2.00    inference(cnf_transformation,[],[f36])).
% 11.47/2.00  
% 11.47/2.00  fof(f63,plain,(
% 11.47/2.00    sK3 = sK4),
% 11.47/2.00    inference(cnf_transformation,[],[f36])).
% 11.47/2.00  
% 11.47/2.00  fof(f6,axiom,(
% 11.47/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 11.47/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/2.00  
% 11.47/2.00  fof(f17,plain,(
% 11.47/2.00    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.47/2.00    inference(ennf_transformation,[],[f6])).
% 11.47/2.00  
% 11.47/2.00  fof(f18,plain,(
% 11.47/2.00    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.47/2.00    inference(flattening,[],[f17])).
% 11.47/2.00  
% 11.47/2.00  fof(f27,plain,(
% 11.47/2.00    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.47/2.00    inference(nnf_transformation,[],[f18])).
% 11.47/2.00  
% 11.47/2.00  fof(f28,plain,(
% 11.47/2.00    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.47/2.00    inference(flattening,[],[f27])).
% 11.47/2.00  
% 11.47/2.00  fof(f47,plain,(
% 11.47/2.00    ( ! [X0,X1] : (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.47/2.00    inference(cnf_transformation,[],[f28])).
% 11.47/2.00  
% 11.47/2.00  fof(f56,plain,(
% 11.47/2.00    l1_pre_topc(sK2)),
% 11.47/2.00    inference(cnf_transformation,[],[f36])).
% 11.47/2.00  
% 11.47/2.00  fof(f4,axiom,(
% 11.47/2.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.47/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/2.00  
% 11.47/2.00  fof(f15,plain,(
% 11.47/2.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.47/2.00    inference(ennf_transformation,[],[f4])).
% 11.47/2.00  
% 11.47/2.00  fof(f44,plain,(
% 11.47/2.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 11.47/2.00    inference(cnf_transformation,[],[f15])).
% 11.47/2.00  
% 11.47/2.00  fof(f3,axiom,(
% 11.47/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 11.47/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/2.00  
% 11.47/2.00  fof(f14,plain,(
% 11.47/2.00    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.47/2.00    inference(ennf_transformation,[],[f3])).
% 11.47/2.00  
% 11.47/2.00  fof(f43,plain,(
% 11.47/2.00    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.47/2.00    inference(cnf_transformation,[],[f14])).
% 11.47/2.00  
% 11.47/2.00  fof(f1,axiom,(
% 11.47/2.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 11.47/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/2.00  
% 11.47/2.00  fof(f10,plain,(
% 11.47/2.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 11.47/2.00    inference(ennf_transformation,[],[f1])).
% 11.47/2.00  
% 11.47/2.00  fof(f11,plain,(
% 11.47/2.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 11.47/2.00    inference(flattening,[],[f10])).
% 11.47/2.00  
% 11.47/2.00  fof(f37,plain,(
% 11.47/2.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 11.47/2.00    inference(cnf_transformation,[],[f11])).
% 11.47/2.00  
% 11.47/2.00  fof(f42,plain,(
% 11.47/2.00    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.47/2.00    inference(cnf_transformation,[],[f14])).
% 11.47/2.00  
% 11.47/2.00  fof(f5,axiom,(
% 11.47/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 11.47/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/2.00  
% 11.47/2.00  fof(f16,plain,(
% 11.47/2.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.47/2.00    inference(ennf_transformation,[],[f5])).
% 11.47/2.00  
% 11.47/2.00  fof(f45,plain,(
% 11.47/2.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.47/2.00    inference(cnf_transformation,[],[f16])).
% 11.47/2.00  
% 11.47/2.00  fof(f2,axiom,(
% 11.47/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 11.47/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/2.00  
% 11.47/2.00  fof(f12,plain,(
% 11.47/2.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.47/2.00    inference(ennf_transformation,[],[f2])).
% 11.47/2.00  
% 11.47/2.00  fof(f13,plain,(
% 11.47/2.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.47/2.00    inference(flattening,[],[f12])).
% 11.47/2.00  
% 11.47/2.00  fof(f23,plain,(
% 11.47/2.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.47/2.00    inference(nnf_transformation,[],[f13])).
% 11.47/2.00  
% 11.47/2.00  fof(f24,plain,(
% 11.47/2.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.47/2.00    inference(rectify,[],[f23])).
% 11.47/2.00  
% 11.47/2.00  fof(f25,plain,(
% 11.47/2.00    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 11.47/2.00    introduced(choice_axiom,[])).
% 11.47/2.00  
% 11.47/2.00  fof(f26,plain,(
% 11.47/2.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.47/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 11.47/2.00  
% 11.47/2.00  fof(f38,plain,(
% 11.47/2.00    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 11.47/2.00    inference(cnf_transformation,[],[f26])).
% 11.47/2.00  
% 11.47/2.00  fof(f41,plain,(
% 11.47/2.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 11.47/2.00    inference(cnf_transformation,[],[f26])).
% 11.47/2.00  
% 11.47/2.00  fof(f55,plain,(
% 11.47/2.00    v2_pre_topc(sK2)),
% 11.47/2.00    inference(cnf_transformation,[],[f36])).
% 11.47/2.00  
% 11.47/2.00  fof(f54,plain,(
% 11.47/2.00    l1_pre_topc(sK1)),
% 11.47/2.00    inference(cnf_transformation,[],[f36])).
% 11.47/2.00  
% 11.47/2.00  fof(f62,plain,(
% 11.47/2.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))),
% 11.47/2.00    inference(cnf_transformation,[],[f36])).
% 11.47/2.00  
% 11.47/2.00  fof(f39,plain,(
% 11.47/2.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 11.47/2.00    inference(cnf_transformation,[],[f26])).
% 11.47/2.00  
% 11.47/2.00  fof(f60,plain,(
% 11.47/2.00    v1_funct_1(sK4)),
% 11.47/2.00    inference(cnf_transformation,[],[f36])).
% 11.47/2.00  
% 11.47/2.00  fof(f61,plain,(
% 11.47/2.00    v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))),
% 11.47/2.00    inference(cnf_transformation,[],[f36])).
% 11.47/2.00  
% 11.47/2.00  fof(f49,plain,(
% 11.47/2.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.47/2.00    inference(cnf_transformation,[],[f28])).
% 11.47/2.00  
% 11.47/2.00  fof(f40,plain,(
% 11.47/2.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v4_pre_topc(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 11.47/2.00    inference(cnf_transformation,[],[f26])).
% 11.47/2.00  
% 11.47/2.00  fof(f65,plain,(
% 11.47/2.00    ~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(sK3,sK1,sK2)),
% 11.47/2.00    inference(cnf_transformation,[],[f36])).
% 11.47/2.00  
% 11.47/2.00  fof(f59,plain,(
% 11.47/2.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 11.47/2.00    inference(cnf_transformation,[],[f36])).
% 11.47/2.00  
% 11.47/2.00  fof(f58,plain,(
% 11.47/2.00    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 11.47/2.00    inference(cnf_transformation,[],[f36])).
% 11.47/2.00  
% 11.47/2.00  fof(f7,axiom,(
% 11.47/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 11.47/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/2.00  
% 11.47/2.00  fof(f19,plain,(
% 11.47/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.47/2.00    inference(ennf_transformation,[],[f7])).
% 11.47/2.00  
% 11.47/2.00  fof(f20,plain,(
% 11.47/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.47/2.00    inference(flattening,[],[f19])).
% 11.47/2.00  
% 11.47/2.00  fof(f29,plain,(
% 11.47/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.47/2.00    inference(nnf_transformation,[],[f20])).
% 11.47/2.00  
% 11.47/2.00  fof(f52,plain,(
% 11.47/2.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.47/2.00    inference(cnf_transformation,[],[f29])).
% 11.47/2.00  
% 11.47/2.00  fof(f66,plain,(
% 11.47/2.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.47/2.00    inference(equality_resolution,[],[f52])).
% 11.47/2.00  
% 11.47/2.00  fof(f53,plain,(
% 11.47/2.00    v2_pre_topc(sK1)),
% 11.47/2.00    inference(cnf_transformation,[],[f36])).
% 11.47/2.00  
% 11.47/2.00  fof(f51,plain,(
% 11.47/2.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.47/2.00    inference(cnf_transformation,[],[f29])).
% 11.47/2.00  
% 11.47/2.00  fof(f67,plain,(
% 11.47/2.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.47/2.00    inference(equality_resolution,[],[f51])).
% 11.47/2.00  
% 11.47/2.00  cnf(c_17,negated_conjecture,
% 11.47/2.00      ( v5_pre_topc(sK3,sK1,sK2)
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 11.47/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1526,plain,
% 11.47/2.00      ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_18,negated_conjecture,
% 11.47/2.00      ( sK3 = sK4 ),
% 11.47/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1547,plain,
% 11.47/2.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 11.47/2.00      inference(light_normalisation,[status(thm)],[c_1526,c_18]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_13,plain,
% 11.47/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.47/2.00      | ~ v4_pre_topc(X0,X1)
% 11.47/2.00      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.47/2.00      | ~ v2_pre_topc(X1)
% 11.47/2.00      | ~ l1_pre_topc(X1) ),
% 11.47/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1530,plain,
% 11.47/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.47/2.00      | v4_pre_topc(X0,X1) != iProver_top
% 11.47/2.00      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 11.47/2.00      | v2_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_25,negated_conjecture,
% 11.47/2.00      ( l1_pre_topc(sK2) ),
% 11.47/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1519,plain,
% 11.47/2.00      ( l1_pre_topc(sK2) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_7,plain,
% 11.47/2.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 11.47/2.00      | ~ l1_pre_topc(X0) ),
% 11.47/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1536,plain,
% 11.47/2.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 11.47/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_5,plain,
% 11.47/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 11.47/2.00      inference(cnf_transformation,[],[f43]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1538,plain,
% 11.47/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1884,plain,
% 11.47/2.00      ( l1_pre_topc(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_1536,c_1538]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_0,plain,
% 11.47/2.00      ( ~ l1_pre_topc(X0)
% 11.47/2.00      | ~ v1_pre_topc(X0)
% 11.47/2.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 11.47/2.00      inference(cnf_transformation,[],[f37]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1543,plain,
% 11.47/2.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 11.47/2.00      | l1_pre_topc(X0) != iProver_top
% 11.47/2.00      | v1_pre_topc(X0) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_2145,plain,
% 11.47/2.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 11.47/2.00      | l1_pre_topc(X0) != iProver_top
% 11.47/2.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_1884,c_1543]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_6,plain,
% 11.47/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.47/2.00      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 11.47/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1537,plain,
% 11.47/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 11.47/2.00      | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1879,plain,
% 11.47/2.00      ( l1_pre_topc(X0) != iProver_top
% 11.47/2.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_1536,c_1537]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_2562,plain,
% 11.47/2.00      ( l1_pre_topc(X0) != iProver_top
% 11.47/2.00      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_2145,c_1879]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_2563,plain,
% 11.47/2.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 11.47/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.47/2.00      inference(renaming,[status(thm)],[c_2562]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_2568,plain,
% 11.47/2.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_1519,c_2563]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_9,plain,
% 11.47/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.47/2.00      | X2 = X1
% 11.47/2.00      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 11.47/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1534,plain,
% 11.47/2.00      ( X0 = X1
% 11.47/2.00      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 11.47/2.00      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_2576,plain,
% 11.47/2.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
% 11.47/2.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X0
% 11.47/2.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_2568,c_1534]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_3277,plain,
% 11.47/2.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2)
% 11.47/2.00      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 11.47/2.00      inference(equality_resolution,[status(thm)],[c_2576]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_32,plain,
% 11.47/2.00      ( l1_pre_topc(sK2) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1672,plain,
% 11.47/2.00      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 11.47/2.00      | ~ l1_pre_topc(sK2) ),
% 11.47/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1673,plain,
% 11.47/2.00      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 11.47/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_1672]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4004,plain,
% 11.47/2.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_3277,c_32,c_1673]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4,plain,
% 11.47/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.47/2.00      | ~ v5_pre_topc(X0,X1,X2)
% 11.47/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.47/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 11.47/2.00      | ~ v4_pre_topc(X3,X2)
% 11.47/2.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 11.47/2.00      | ~ v1_funct_1(X0)
% 11.47/2.00      | ~ l1_pre_topc(X1)
% 11.47/2.00      | ~ l1_pre_topc(X2) ),
% 11.47/2.00      inference(cnf_transformation,[],[f38]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1539,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,X2) != iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 11.47/2.00      | v4_pre_topc(X3,X2) != iProver_top
% 11.47/2.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1) = iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(X2) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4039,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
% 11.47/2.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
% 11.47/2.00      | v4_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),X1) = iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_4004,c_1539]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4090,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.47/2.00      | v4_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),X1) = iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 11.47/2.00      inference(light_normalisation,[status(thm)],[c_4039,c_4004]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1638,plain,
% 11.47/2.00      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 11.47/2.00      inference(instantiation,[status(thm)],[c_5]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1639,plain,
% 11.47/2.00      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_1638]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_8913,plain,
% 11.47/2.00      ( l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),X1) = iProver_top
% 11.47/2.00      | v4_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_4090,c_32,c_1639,c_1673]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_8914,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.47/2.00      | v4_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),X1) = iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.47/2.00      inference(renaming,[status(thm)],[c_8913]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1,plain,
% 11.47/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.47/2.00      | v5_pre_topc(X0,X1,X2)
% 11.47/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.47/2.00      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 11.47/2.00      | ~ v1_funct_1(X0)
% 11.47/2.00      | ~ l1_pre_topc(X1)
% 11.47/2.00      | ~ l1_pre_topc(X2) ),
% 11.47/2.00      inference(cnf_transformation,[],[f41]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1542,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,X2) = iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 11.47/2.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(X2) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_8921,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,sK2) = iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(sK0(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(X1,sK2,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_8914,c_1542]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_9188,plain,
% 11.47/2.00      ( l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(X1,sK2,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | m1_subset_1(sK0(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,sK2) = iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_8921,c_32]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_9189,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,sK2) = iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(sK0(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(X1,sK2,X0),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.47/2.00      inference(renaming,[status(thm)],[c_9188]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_9194,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,sK2) = iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(sK0(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(X1,sK2,X0),sK2) != iProver_top
% 11.47/2.00      | v2_pre_topc(sK2) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_1530,c_9189]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_26,negated_conjecture,
% 11.47/2.00      ( v2_pre_topc(sK2) ),
% 11.47/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_31,plain,
% 11.47/2.00      ( v2_pre_topc(sK2) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_9305,plain,
% 11.47/2.00      ( l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,sK2) = iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(sK0(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(X1,sK2,X0),sK2) != iProver_top ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_9194,c_31,c_32]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_9306,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,sK2) = iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(sK0(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(X1,sK2,X0),sK2) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.47/2.00      inference(renaming,[status(thm)],[c_9305]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_9312,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 11.47/2.00      | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.47/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) != iProver_top
% 11.47/2.00      | v1_funct_1(sK4) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_1547,c_9306]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_27,negated_conjecture,
% 11.47/2.00      ( l1_pre_topc(sK1) ),
% 11.47/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1517,plain,
% 11.47/2.00      ( l1_pre_topc(sK1) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_2569,plain,
% 11.47/2.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_1517,c_2563]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_2649,plain,
% 11.47/2.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 11.47/2.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
% 11.47/2.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_2569,c_1534]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_3375,plain,
% 11.47/2.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1)
% 11.47/2.00      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 11.47/2.00      inference(equality_resolution,[status(thm)],[c_2649]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_30,plain,
% 11.47/2.00      ( l1_pre_topc(sK1) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_63,plain,
% 11.47/2.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 11.47/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_65,plain,
% 11.47/2.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 11.47/2.00      | l1_pre_topc(sK1) != iProver_top ),
% 11.47/2.00      inference(instantiation,[status(thm)],[c_63]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4905,plain,
% 11.47/2.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1) ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_3375,c_30,c_65]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_9318,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 11.47/2.00      | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.47/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) != iProver_top
% 11.47/2.00      | v1_funct_1(sK4) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 11.47/2.00      inference(light_normalisation,[status(thm)],[c_9312,c_4905]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_19,negated_conjecture,
% 11.47/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
% 11.47/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1525,plain,
% 11.47/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_3,plain,
% 11.47/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.47/2.00      | v5_pre_topc(X0,X1,X2)
% 11.47/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.47/2.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 11.47/2.00      | ~ v1_funct_1(X0)
% 11.47/2.00      | ~ l1_pre_topc(X1)
% 11.47/2.00      | ~ l1_pre_topc(X2) ),
% 11.47/2.00      inference(cnf_transformation,[],[f39]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1540,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,X2) = iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(X2) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_2931,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
% 11.47/2.00      | v1_funct_1(sK4) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_1525,c_1540]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_21,negated_conjecture,
% 11.47/2.00      ( v1_funct_1(sK4) ),
% 11.47/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_36,plain,
% 11.47/2.00      ( v1_funct_1(sK4) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_20,negated_conjecture,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
% 11.47/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_37,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1760,plain,
% 11.47/2.00      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 11.47/2.00      inference(instantiation,[status(thm)],[c_5]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1761,plain,
% 11.47/2.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_1760]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_3222,plain,
% 11.47/2.00      ( m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_2931,c_30,c_32,c_36,c_37,c_65,c_1639,c_1673,c_1761]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_3223,plain,
% 11.47/2.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top ),
% 11.47/2.00      inference(renaming,[status(thm)],[c_3222]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_11,plain,
% 11.47/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 11.47/2.00      | v4_pre_topc(X0,X1)
% 11.47/2.00      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.47/2.00      | ~ v2_pre_topc(X1)
% 11.47/2.00      | ~ l1_pre_topc(X1) ),
% 11.47/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1532,plain,
% 11.47/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 11.47/2.00      | v4_pre_topc(X0,X1) = iProver_top
% 11.47/2.00      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 11.47/2.00      | v2_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_3227,plain,
% 11.47/2.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),sK2) = iProver_top
% 11.47/2.00      | v2_pre_topc(sK2) != iProver_top
% 11.47/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_3223,c_1532]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_2,plain,
% 11.47/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.47/2.00      | v5_pre_topc(X0,X1,X2)
% 11.47/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.47/2.00      | v4_pre_topc(sK0(X1,X2,X0),X2)
% 11.47/2.00      | ~ v1_funct_1(X0)
% 11.47/2.00      | ~ l1_pre_topc(X1)
% 11.47/2.00      | ~ l1_pre_topc(X2) ),
% 11.47/2.00      inference(cnf_transformation,[],[f40]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1541,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,X2) = iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(X1,X2,X0),X2) = iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(X2) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_2926,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | v1_funct_1(sK4) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_1525,c_1541]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_3217,plain,
% 11.47/2.00      ( v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_2926,c_30,c_32,c_36,c_37,c_65,c_1639,c_1673,c_1761]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_3218,plain,
% 11.47/2.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 11.47/2.00      inference(renaming,[status(thm)],[c_3217]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_3710,plain,
% 11.47/2.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),sK2) = iProver_top ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_3227,c_31,c_32,c_3218]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4038,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
% 11.47/2.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X1) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_4004,c_1542]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4091,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X1) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 11.47/2.00      inference(light_normalisation,[status(thm)],[c_4038,c_4004]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_7472,plain,
% 11.47/2.00      ( l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X1) != iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_4091,c_32,c_1639,c_1673]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_7473,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)),X1) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.47/2.00      inference(renaming,[status(thm)],[c_7472]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_7478,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,sK2) != iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK2) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_1539,c_7473]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4040,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_4004,c_1540]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4089,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 11.47/2.00      inference(light_normalisation,[status(thm)],[c_4040,c_4004]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_7661,plain,
% 11.47/2.00      ( l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK2) != iProver_top
% 11.47/2.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,sK2) != iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_7478,c_32,c_1639,c_1673,c_4089]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_7662,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,sK2) != iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),sK2) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.47/2.00      inference(renaming,[status(thm)],[c_7661]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_7667,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 11.47/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | v1_funct_1(sK4) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_3710,c_7662]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_7668,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 11.47/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | v1_funct_1(sK4) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 11.47/2.00      inference(light_normalisation,[status(thm)],[c_7667,c_4905]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_16,negated_conjecture,
% 11.47/2.00      ( ~ v5_pre_topc(sK3,sK1,sK2)
% 11.47/2.00      | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 11.47/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1527,plain,
% 11.47/2.00      ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1548,plain,
% 11.47/2.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
% 11.47/2.00      inference(light_normalisation,[status(thm)],[c_1527,c_18]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_22,negated_conjecture,
% 11.47/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 11.47/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1522,plain,
% 11.47/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1546,plain,
% 11.47/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 11.47/2.00      inference(light_normalisation,[status(thm)],[c_1522,c_18]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_23,negated_conjecture,
% 11.47/2.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 11.47/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1521,plain,
% 11.47/2.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1545,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 11.47/2.00      inference(light_normalisation,[status(thm)],[c_1521,c_18]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4017,plain,
% 11.47/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) = iProver_top ),
% 11.47/2.00      inference(demodulation,[status(thm)],[c_4004,c_1525]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_14,plain,
% 11.47/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.47/2.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 11.47/2.00      | v5_pre_topc(X0,X1,X2)
% 11.47/2.00      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 11.47/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.47/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 11.47/2.00      | ~ v2_pre_topc(X1)
% 11.47/2.00      | ~ v2_pre_topc(X2)
% 11.47/2.00      | ~ v1_funct_1(X0)
% 11.47/2.00      | ~ l1_pre_topc(X1)
% 11.47/2.00      | ~ l1_pre_topc(X2) ),
% 11.47/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1529,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 11.47/2.00      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,X2) = iProver_top
% 11.47/2.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 11.47/2.00      | v2_pre_topc(X1) != iProver_top
% 11.47/2.00      | v2_pre_topc(X2) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(X2) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4249,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 11.47/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | v2_pre_topc(sK2) != iProver_top
% 11.47/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.47/2.00      | v1_funct_1(sK4) != iProver_top
% 11.47/2.00      | l1_pre_topc(sK2) != iProver_top
% 11.47/2.00      | l1_pre_topc(sK1) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_4017,c_1529]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_28,negated_conjecture,
% 11.47/2.00      ( v2_pre_topc(sK1) ),
% 11.47/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_29,plain,
% 11.47/2.00      ( v2_pre_topc(sK1) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_2865,plain,
% 11.47/2.00      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK2))
% 11.47/2.00      | ~ v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2))
% 11.47/2.00      | v5_pre_topc(sK4,X0,sK2)
% 11.47/2.00      | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2)
% 11.47/2.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
% 11.47/2.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2))))
% 11.47/2.00      | ~ v2_pre_topc(X0)
% 11.47/2.00      | ~ v2_pre_topc(sK2)
% 11.47/2.00      | ~ v1_funct_1(sK4)
% 11.47/2.00      | ~ l1_pre_topc(X0)
% 11.47/2.00      | ~ l1_pre_topc(sK2) ),
% 11.47/2.00      inference(instantiation,[status(thm)],[c_14]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_2881,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,X0,sK2) = iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) != iProver_top
% 11.47/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | v2_pre_topc(X0) != iProver_top
% 11.47/2.00      | v2_pre_topc(sK2) != iProver_top
% 11.47/2.00      | v1_funct_1(sK4) != iProver_top
% 11.47/2.00      | l1_pre_topc(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_2865]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_2883,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 11.47/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | v2_pre_topc(sK2) != iProver_top
% 11.47/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.47/2.00      | v1_funct_1(sK4) != iProver_top
% 11.47/2.00      | l1_pre_topc(sK2) != iProver_top
% 11.47/2.00      | l1_pre_topc(sK1) != iProver_top ),
% 11.47/2.00      inference(instantiation,[status(thm)],[c_2881]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1524,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4018,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) = iProver_top ),
% 11.47/2.00      inference(demodulation,[status(thm)],[c_4004,c_1524]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4719,plain,
% 11.47/2.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_4249,c_29,c_30,c_31,c_32,c_36,c_1546,c_1545,c_2883,
% 11.47/2.00                 c_4017,c_4018]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_7890,plain,
% 11.47/2.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_7668,c_30,c_36,c_65,c_1548,c_1546,c_1545,c_1761,
% 11.47/2.00                 c_4719]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4247,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 11.47/2.00      | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 11.47/2.00      | v1_funct_1(sK4) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 11.47/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_4017,c_1540]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4822,plain,
% 11.47/2.00      ( m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_4247,c_30,c_32,c_36,c_65,c_1761,c_4018]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4823,plain,
% 11.47/2.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 11.47/2.00      | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 11.47/2.00      inference(renaming,[status(thm)],[c_4822]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_15,plain,
% 11.47/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.47/2.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 11.47/2.00      | ~ v5_pre_topc(X0,X1,X2)
% 11.47/2.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 11.47/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.47/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 11.47/2.00      | ~ v2_pre_topc(X1)
% 11.47/2.00      | ~ v2_pre_topc(X2)
% 11.47/2.00      | ~ v1_funct_1(X0)
% 11.47/2.00      | ~ l1_pre_topc(X1)
% 11.47/2.00      | ~ l1_pre_topc(X2) ),
% 11.47/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_1528,plain,
% 11.47/2.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 11.47/2.00      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,X1,X2) != iProver_top
% 11.47/2.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 11.47/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 11.47/2.00      | v2_pre_topc(X1) != iProver_top
% 11.47/2.00      | v2_pre_topc(X2) != iProver_top
% 11.47/2.00      | v1_funct_1(X0) != iProver_top
% 11.47/2.00      | l1_pre_topc(X1) != iProver_top
% 11.47/2.00      | l1_pre_topc(X2) != iProver_top ),
% 11.47/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4250,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,sK1,sK2) != iProver_top
% 11.47/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 11.47/2.00      | v2_pre_topc(sK2) != iProver_top
% 11.47/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.47/2.00      | v1_funct_1(sK4) != iProver_top
% 11.47/2.00      | l1_pre_topc(sK2) != iProver_top
% 11.47/2.00      | l1_pre_topc(sK1) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_4017,c_1528]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4811,plain,
% 11.47/2.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_4250,c_29,c_30,c_31,c_32,c_36,c_1546,c_1545,c_4018]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4248,plain,
% 11.47/2.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top
% 11.47/2.00      | v1_funct_1(sK4) != iProver_top
% 11.47/2.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 11.47/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.47/2.00      inference(superposition,[status(thm)],[c_4017,c_1541]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4714,plain,
% 11.47/2.00      ( v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top
% 11.47/2.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
% 11.47/2.00      inference(global_propositional_subsumption,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_4248,c_30,c_32,c_36,c_65,c_1761,c_4018]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(c_4715,plain,
% 11.47/2.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 11.47/2.00      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top ),
% 11.47/2.00      inference(renaming,[status(thm)],[c_4714]) ).
% 11.47/2.00  
% 11.47/2.00  cnf(contradiction,plain,
% 11.47/2.00      ( $false ),
% 11.47/2.00      inference(minisat,
% 11.47/2.00                [status(thm)],
% 11.47/2.00                [c_9318,c_7890,c_4823,c_4811,c_4715,c_1761,c_1545,c_1546,
% 11.47/2.00                 c_65,c_36,c_30]) ).
% 11.47/2.00  
% 11.47/2.00  
% 11.47/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.47/2.00  
% 11.47/2.00  ------                               Statistics
% 11.47/2.00  
% 11.47/2.00  ------ General
% 11.47/2.00  
% 11.47/2.00  abstr_ref_over_cycles:                  0
% 11.47/2.00  abstr_ref_under_cycles:                 0
% 11.47/2.00  gc_basic_clause_elim:                   0
% 11.47/2.00  forced_gc_time:                         0
% 11.47/2.00  parsing_time:                           0.009
% 11.47/2.00  unif_index_cands_time:                  0.
% 11.47/2.00  unif_index_add_time:                    0.
% 11.47/2.00  orderings_time:                         0.
% 11.47/2.00  out_proof_time:                         0.015
% 11.47/2.00  total_time:                             1.099
% 11.47/2.00  num_of_symbols:                         50
% 11.47/2.00  num_of_terms:                           12362
% 11.47/2.00  
% 11.47/2.00  ------ Preprocessing
% 11.47/2.00  
% 11.47/2.00  num_of_splits:                          0
% 11.47/2.00  num_of_split_atoms:                     0
% 11.47/2.00  num_of_reused_defs:                     0
% 11.47/2.00  num_eq_ax_congr_red:                    8
% 11.47/2.00  num_of_sem_filtered_clauses:            1
% 11.47/2.00  num_of_subtypes:                        0
% 11.47/2.00  monotx_restored_types:                  0
% 11.47/2.00  sat_num_of_epr_types:                   0
% 11.47/2.00  sat_num_of_non_cyclic_types:            0
% 11.47/2.00  sat_guarded_non_collapsed_types:        0
% 11.47/2.00  num_pure_diseq_elim:                    0
% 11.47/2.00  simp_replaced_by:                       0
% 11.47/2.00  res_preprocessed:                       120
% 11.47/2.00  prep_upred:                             0
% 11.47/2.00  prep_unflattend:                        13
% 11.47/2.00  smt_new_axioms:                         0
% 11.47/2.00  pred_elim_cands:                        8
% 11.47/2.00  pred_elim:                              0
% 11.47/2.00  pred_elim_cl:                           0
% 11.47/2.00  pred_elim_cycles:                       2
% 11.47/2.00  merged_defs:                            6
% 11.47/2.00  merged_defs_ncl:                        0
% 11.47/2.00  bin_hyper_res:                          6
% 11.47/2.00  prep_cycles:                            3
% 11.47/2.00  pred_elim_time:                         0.011
% 11.47/2.00  splitting_time:                         0.
% 11.47/2.00  sem_filter_time:                        0.
% 11.47/2.00  monotx_time:                            0.001
% 11.47/2.00  subtype_inf_time:                       0.
% 11.47/2.00  
% 11.47/2.00  ------ Problem properties
% 11.47/2.00  
% 11.47/2.00  clauses:                                29
% 11.47/2.00  conjectures:                            13
% 11.47/2.00  epr:                                    7
% 11.47/2.00  horn:                                   26
% 11.47/2.00  ground:                                 13
% 11.47/2.00  unary:                                  11
% 11.47/2.00  binary:                                 5
% 11.47/2.00  lits:                                   102
% 11.47/2.00  lits_eq:                                6
% 11.47/2.00  fd_pure:                                0
% 11.47/2.00  fd_pseudo:                              0
% 11.47/2.00  fd_cond:                                0
% 11.47/2.00  fd_pseudo_cond:                         2
% 11.47/2.00  ac_symbols:                             0
% 11.47/2.00  
% 11.47/2.00  ------ Propositional Solver
% 11.47/2.00  
% 11.47/2.00  prop_solver_calls:                      30
% 11.47/2.00  prop_fast_solver_calls:                 2042
% 11.47/2.00  smt_solver_calls:                       0
% 11.47/2.00  smt_fast_solver_calls:                  0
% 11.47/2.00  prop_num_of_clauses:                    3490
% 11.47/2.00  prop_preprocess_simplified:             7105
% 11.47/2.00  prop_fo_subsumed:                       147
% 11.47/2.00  prop_solver_time:                       0.
% 11.47/2.00  smt_solver_time:                        0.
% 11.47/2.00  smt_fast_solver_time:                   0.
% 11.47/2.00  prop_fast_solver_time:                  0.
% 11.47/2.00  prop_unsat_core_time:                   0.
% 11.47/2.00  
% 11.47/2.00  ------ QBF
% 11.47/2.00  
% 11.47/2.00  qbf_q_res:                              0
% 11.47/2.00  qbf_num_tautologies:                    0
% 11.47/2.00  qbf_prep_cycles:                        0
% 11.47/2.00  
% 11.47/2.00  ------ BMC1
% 11.47/2.00  
% 11.47/2.00  bmc1_current_bound:                     -1
% 11.47/2.00  bmc1_last_solved_bound:                 -1
% 11.47/2.00  bmc1_unsat_core_size:                   -1
% 11.47/2.00  bmc1_unsat_core_parents_size:           -1
% 11.47/2.00  bmc1_merge_next_fun:                    0
% 11.47/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.47/2.00  
% 11.47/2.00  ------ Instantiation
% 11.47/2.00  
% 11.47/2.00  inst_num_of_clauses:                    894
% 11.47/2.00  inst_num_in_passive:                    218
% 11.47/2.00  inst_num_in_active:                     608
% 11.47/2.00  inst_num_in_unprocessed:                68
% 11.47/2.00  inst_num_of_loops:                      670
% 11.47/2.00  inst_num_of_learning_restarts:          0
% 11.47/2.00  inst_num_moves_active_passive:          55
% 11.47/2.00  inst_lit_activity:                      0
% 11.47/2.00  inst_lit_activity_moves:                0
% 11.47/2.00  inst_num_tautologies:                   0
% 11.47/2.00  inst_num_prop_implied:                  0
% 11.47/2.00  inst_num_existing_simplified:           0
% 11.47/2.00  inst_num_eq_res_simplified:             0
% 11.47/2.00  inst_num_child_elim:                    0
% 11.47/2.00  inst_num_of_dismatching_blockings:      801
% 11.47/2.00  inst_num_of_non_proper_insts:           1817
% 11.47/2.00  inst_num_of_duplicates:                 0
% 11.47/2.00  inst_inst_num_from_inst_to_res:         0
% 11.47/2.00  inst_dismatching_checking_time:         0.
% 11.47/2.00  
% 11.47/2.00  ------ Resolution
% 11.47/2.00  
% 11.47/2.00  res_num_of_clauses:                     0
% 11.47/2.00  res_num_in_passive:                     0
% 11.47/2.00  res_num_in_active:                      0
% 11.47/2.00  res_num_of_loops:                       123
% 11.47/2.00  res_forward_subset_subsumed:            122
% 11.47/2.00  res_backward_subset_subsumed:           0
% 11.47/2.00  res_forward_subsumed:                   0
% 11.47/2.00  res_backward_subsumed:                  0
% 11.47/2.00  res_forward_subsumption_resolution:     0
% 11.47/2.00  res_backward_subsumption_resolution:    0
% 11.47/2.00  res_clause_to_clause_subsumption:       1112
% 11.47/2.00  res_orphan_elimination:                 0
% 11.47/2.00  res_tautology_del:                      118
% 11.47/2.00  res_num_eq_res_simplified:              0
% 11.47/2.00  res_num_sel_changes:                    0
% 11.47/2.00  res_moves_from_active_to_pass:          0
% 11.47/2.00  
% 11.47/2.00  ------ Superposition
% 11.47/2.00  
% 11.47/2.00  sup_time_total:                         0.
% 11.47/2.00  sup_time_generating:                    0.
% 11.47/2.00  sup_time_sim_full:                      0.
% 11.47/2.00  sup_time_sim_immed:                     0.
% 11.47/2.00  
% 11.47/2.00  sup_num_of_clauses:                     174
% 11.47/2.00  sup_num_in_active:                      100
% 11.47/2.00  sup_num_in_passive:                     74
% 11.47/2.00  sup_num_of_loops:                       132
% 11.47/2.00  sup_fw_superposition:                   1317
% 11.47/2.00  sup_bw_superposition:                   185
% 11.47/2.00  sup_immediate_simplified:               248
% 11.47/2.00  sup_given_eliminated:                   5
% 11.47/2.00  comparisons_done:                       0
% 11.47/2.00  comparisons_avoided:                    0
% 11.47/2.00  
% 11.47/2.00  ------ Simplifications
% 11.47/2.00  
% 11.47/2.00  
% 11.47/2.00  sim_fw_subset_subsumed:                 2
% 11.47/2.00  sim_bw_subset_subsumed:                 22
% 11.47/2.00  sim_fw_subsumed:                        37
% 11.47/2.00  sim_bw_subsumed:                        8
% 11.47/2.00  sim_fw_subsumption_res:                 0
% 11.47/2.00  sim_bw_subsumption_res:                 0
% 11.47/2.00  sim_tautology_del:                      64
% 11.47/2.00  sim_eq_tautology_del:                   24
% 11.47/2.00  sim_eq_res_simp:                        0
% 11.47/2.00  sim_fw_demodulated:                     2
% 11.47/2.00  sim_bw_demodulated:                     24
% 11.47/2.00  sim_light_normalised:                   281
% 11.47/2.00  sim_joinable_taut:                      0
% 11.47/2.00  sim_joinable_simp:                      0
% 11.47/2.00  sim_ac_normalised:                      0
% 11.47/2.00  sim_smt_subsumption:                    0
% 11.47/2.00  
%------------------------------------------------------------------------------
