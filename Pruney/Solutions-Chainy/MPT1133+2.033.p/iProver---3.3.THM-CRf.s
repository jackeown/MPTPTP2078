%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:55 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  286 (37134 expanded)
%              Number of clauses        :  197 (8269 expanded)
%              Number of leaves         :   21 (11150 expanded)
%              Depth                    :   33
%              Number of atoms          : 1269 (437138 expanded)
%              Number of equality atoms :  485 (49486 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f50,f49,f48,f47])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
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
    inference(equality_resolution,[],[f74])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
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
    inference(equality_resolution,[],[f73])).

fof(f77,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
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
    inference(pure_predicate_removal,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f72,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f70,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f99,plain,(
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
    inference(equality_resolution,[],[f76])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,(
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
    inference(equality_resolution,[],[f75])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2343,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_27,negated_conjecture,
    ( sK2 = sK3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2385,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2343,c_27])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2363,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4298,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2385,c_2363])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2342,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2382,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2342,c_27])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2357,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4402,plain,
    ( k1_relset_1(X0,u1_struct_0(sK1),sK3) = X0
    | u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK3,X0,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4298,c_2357])).

cnf(c_5576,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2382,c_4402])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2364,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3732,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2385,c_2364])).

cnf(c_5581,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5576,c_3732])).

cnf(c_4401,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2385,c_2357])).

cnf(c_4414,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4401,c_3732])).

cnf(c_6120,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5581,c_2382,c_4414])).

cnf(c_6121,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_6120])).

cnf(c_6168,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6121,c_2385])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2361,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6830,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6168,c_2361])).

cnf(c_6169,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6121,c_2382])).

cnf(c_7607,plain,
    ( sK3 = k1_xboole_0
    | u1_struct_0(sK0) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6830,c_6169])).

cnf(c_7608,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7607])).

cnf(c_7653,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7608,c_2385])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_45,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_47,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2707,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3320,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2707])).

cnf(c_3321,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3320])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2708,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3565,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2708])).

cnf(c_3566,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3565])).

cnf(c_4997,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | k1_relset_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_16,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2736,plain,
    ( v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k1_relset_1(X0,X1,sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_5007,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_1(sK3)
    | k1_relset_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2736])).

cnf(c_5008,plain,
    ( k1_relset_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) != k1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5007])).

cnf(c_2346,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f97])).

cnf(c_2352,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5150,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_2352])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_6,c_4])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_497,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_5])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_497])).

cnf(c_2336,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_498])).

cnf(c_2816,plain,
    ( r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2385,c_2336])).

cnf(c_4297,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_2363])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f98])).

cnf(c_2351,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5064,plain,
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
    inference(superposition,[status(thm)],[c_2346,c_2351])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_38,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_39,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_46,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2348,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2431,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2348,c_27])).

cnf(c_26,negated_conjecture,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2347,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2426,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2347,c_27])).

cnf(c_19,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2645,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2646,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2645])).

cnf(c_20,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2651,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2652,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2651])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2797,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2798,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2797])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f99])).

cnf(c_2782,plain,
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
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3229,plain,
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
    inference(instantiation,[status(thm)],[c_2782])).

cnf(c_3719,plain,
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
    inference(instantiation,[status(thm)],[c_3229])).

cnf(c_3720,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3719])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f100])).

cnf(c_2792,plain,
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
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3269,plain,
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
    inference(instantiation,[status(thm)],[c_2792])).

cnf(c_3755,plain,
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
    inference(instantiation,[status(thm)],[c_3269])).

cnf(c_3756,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3755])).

cnf(c_5299,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5064,c_38,c_39,c_40,c_41,c_45,c_46,c_2431,c_2385,c_2426,c_2382,c_2646,c_2652,c_2798,c_3720,c_3756,c_5150])).

cnf(c_5300,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5299])).

cnf(c_5303,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5300,c_38,c_39,c_40,c_41,c_45,c_46,c_2385,c_2426,c_2382,c_2646,c_2652,c_2798,c_3756,c_5150])).

cnf(c_5309,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4297,c_5303])).

cnf(c_5367,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5150,c_2816,c_5309])).

cnf(c_7638,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7608,c_5367])).

cnf(c_8001,plain,
    ( sK3 = k1_xboole_0
    | u1_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7653,c_45,c_28,c_47,c_3320,c_3321,c_3565,c_3566,c_4997,c_5008,c_7638])).

cnf(c_8002,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8001])).

cnf(c_3127,plain,
    ( r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_2336])).

cnf(c_4350,plain,
    ( k1_relset_1(X0,u1_struct_0(sK1),sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4298,c_2364])).

cnf(c_4966,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3127,c_4350])).

cnf(c_2356,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | v1_funct_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4973,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4966,c_2356])).

cnf(c_2691,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_2692,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2691])).

cnf(c_2350,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4388,plain,
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
    inference(superposition,[status(thm)],[c_2346,c_2350])).

cnf(c_2648,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2649,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2648])).

cnf(c_2654,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2655,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2654])).

cnf(c_2805,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2806,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2805])).

cnf(c_2772,plain,
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
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3189,plain,
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
    inference(instantiation,[status(thm)],[c_2772])).

cnf(c_3695,plain,
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
    inference(instantiation,[status(thm)],[c_3189])).

cnf(c_3696,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3695])).

cnf(c_2349,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3810,plain,
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
    inference(superposition,[status(thm)],[c_2346,c_2349])).

cnf(c_2762,plain,
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
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3149,plain,
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
    inference(instantiation,[status(thm)],[c_2762])).

cnf(c_3671,plain,
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
    inference(instantiation,[status(thm)],[c_3149])).

cnf(c_3672,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3671])).

cnf(c_4198,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3810,c_38,c_39,c_40,c_41,c_45,c_46,c_2431,c_2385,c_2382,c_2649,c_2655,c_2806,c_3672])).

cnf(c_4199,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4198])).

cnf(c_4954,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4388,c_38,c_39,c_40,c_41,c_45,c_46,c_2385,c_2426,c_2382,c_2649,c_2655,c_2806,c_3696,c_4199])).

cnf(c_4955,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4954])).

cnf(c_4960,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4298,c_4955])).

cnf(c_9513,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4973,c_45,c_47,c_2692,c_4960])).

cnf(c_9514,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9513])).

cnf(c_9519,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) != k1_relat_1(sK3)
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8002,c_9514])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_111,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_115,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1580,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3040,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_1581,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3618,plain,
    ( X0 != X1
    | X0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != X1 ),
    inference(instantiation,[status(thm)],[c_1581])).

cnf(c_3619,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3618])).

cnf(c_1587,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_2742,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | X2 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_3774,plain,
    ( v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2742])).

cnf(c_3777,plain,
    ( X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | sK3 != sK3
    | v1_funct_2(sK3,X1,X0) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3774])).

cnf(c_3779,plain,
    ( sK3 != sK3
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3777])).

cnf(c_5511,plain,
    ( X0 != X1
    | X0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != X1 ),
    inference(instantiation,[status(thm)],[c_1581])).

cnf(c_5512,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5511])).

cnf(c_4400,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_2357])).

cnf(c_3731,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2346,c_2364])).

cnf(c_4421,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4400,c_3731])).

cnf(c_4427,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4421])).

cnf(c_8456,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4421,c_29,c_4427])).

cnf(c_8457,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_8456])).

cnf(c_2345,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8499,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8457,c_2345])).

cnf(c_8498,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8457,c_2346])).

cnf(c_9457,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8498,c_2361])).

cnf(c_8033,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8002,c_5367])).

cnf(c_9577,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8457,c_8033])).

cnf(c_9630,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9519,c_46,c_111,c_115,c_3040,c_3619,c_3779,c_5512,c_8457,c_8499,c_9457,c_9514,c_9577])).

cnf(c_9636,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4298,c_9630])).

cnf(c_9817,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9636,c_47,c_2692])).

cnf(c_2366,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3818,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | r1_tarski(u1_struct_0(sK0),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2816,c_2366])).

cnf(c_9864,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | r1_tarski(u1_struct_0(sK0),k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9817,c_3818])).

cnf(c_2365,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4965,plain,
    ( k1_relset_1(k1_relat_1(sK3),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2365,c_4350])).

cnf(c_12,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2359,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5242,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4965,c_2359])).

cnf(c_5241,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4965,c_2356])).

cnf(c_5290,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5242,c_45,c_5241])).

cnf(c_5296,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4298,c_5290])).

cnf(c_5373,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5296,c_3566])).

cnf(c_9851,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9817,c_5373])).

cnf(c_8493,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8457,c_5367])).

cnf(c_9622,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6169,c_8493])).

cnf(c_10972,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_9622,c_9817])).

cnf(c_5046,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4960,c_47,c_2692])).

cnf(c_9855,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9817,c_5046])).

cnf(c_13876,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10972,c_9855])).

cnf(c_14598,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9864,c_9851,c_13876])).

cnf(c_9852,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9817,c_5367])).

cnf(c_14627,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14598,c_9852])).

cnf(c_4872,plain,
    ( k1_relset_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4297,c_2364])).

cnf(c_5013,plain,
    ( k1_relset_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2365,c_4872])).

cnf(c_5258,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5013,c_2356])).

cnf(c_5720,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5258,c_45,c_28,c_47,c_3320,c_3321,c_3565,c_3566,c_4997,c_5008])).

cnf(c_9846,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9817,c_5720])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14627,c_9846])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.79/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/0.99  
% 3.79/0.99  ------  iProver source info
% 3.79/0.99  
% 3.79/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.79/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/0.99  git: non_committed_changes: false
% 3.79/0.99  git: last_make_outside_of_git: false
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options
% 3.79/0.99  
% 3.79/0.99  --out_options                           all
% 3.79/0.99  --tptp_safe_out                         true
% 3.79/0.99  --problem_path                          ""
% 3.79/0.99  --include_path                          ""
% 3.79/0.99  --clausifier                            res/vclausify_rel
% 3.79/0.99  --clausifier_options                    --mode clausify
% 3.79/0.99  --stdin                                 false
% 3.79/0.99  --stats_out                             all
% 3.79/0.99  
% 3.79/0.99  ------ General Options
% 3.79/0.99  
% 3.79/0.99  --fof                                   false
% 3.79/0.99  --time_out_real                         305.
% 3.79/0.99  --time_out_virtual                      -1.
% 3.79/0.99  --symbol_type_check                     false
% 3.79/0.99  --clausify_out                          false
% 3.79/0.99  --sig_cnt_out                           false
% 3.79/0.99  --trig_cnt_out                          false
% 3.79/0.99  --trig_cnt_out_tolerance                1.
% 3.79/0.99  --trig_cnt_out_sk_spl                   false
% 3.79/0.99  --abstr_cl_out                          false
% 3.79/0.99  
% 3.79/0.99  ------ Global Options
% 3.79/0.99  
% 3.79/0.99  --schedule                              default
% 3.79/0.99  --add_important_lit                     false
% 3.79/0.99  --prop_solver_per_cl                    1000
% 3.79/0.99  --min_unsat_core                        false
% 3.79/0.99  --soft_assumptions                      false
% 3.79/0.99  --soft_lemma_size                       3
% 3.79/0.99  --prop_impl_unit_size                   0
% 3.79/0.99  --prop_impl_unit                        []
% 3.79/0.99  --share_sel_clauses                     true
% 3.79/0.99  --reset_solvers                         false
% 3.79/0.99  --bc_imp_inh                            [conj_cone]
% 3.79/0.99  --conj_cone_tolerance                   3.
% 3.79/0.99  --extra_neg_conj                        none
% 3.79/0.99  --large_theory_mode                     true
% 3.79/0.99  --prolific_symb_bound                   200
% 3.79/0.99  --lt_threshold                          2000
% 3.79/0.99  --clause_weak_htbl                      true
% 3.79/0.99  --gc_record_bc_elim                     false
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing Options
% 3.79/0.99  
% 3.79/0.99  --preprocessing_flag                    true
% 3.79/0.99  --time_out_prep_mult                    0.1
% 3.79/0.99  --splitting_mode                        input
% 3.79/0.99  --splitting_grd                         true
% 3.79/0.99  --splitting_cvd                         false
% 3.79/0.99  --splitting_cvd_svl                     false
% 3.79/0.99  --splitting_nvd                         32
% 3.79/0.99  --sub_typing                            true
% 3.79/0.99  --prep_gs_sim                           true
% 3.79/0.99  --prep_unflatten                        true
% 3.79/0.99  --prep_res_sim                          true
% 3.79/0.99  --prep_upred                            true
% 3.79/0.99  --prep_sem_filter                       exhaustive
% 3.79/0.99  --prep_sem_filter_out                   false
% 3.79/0.99  --pred_elim                             true
% 3.79/0.99  --res_sim_input                         true
% 3.79/0.99  --eq_ax_congr_red                       true
% 3.79/0.99  --pure_diseq_elim                       true
% 3.79/0.99  --brand_transform                       false
% 3.79/0.99  --non_eq_to_eq                          false
% 3.79/0.99  --prep_def_merge                        true
% 3.79/0.99  --prep_def_merge_prop_impl              false
% 3.79/0.99  --prep_def_merge_mbd                    true
% 3.79/0.99  --prep_def_merge_tr_red                 false
% 3.79/0.99  --prep_def_merge_tr_cl                  false
% 3.79/0.99  --smt_preprocessing                     true
% 3.79/0.99  --smt_ac_axioms                         fast
% 3.79/0.99  --preprocessed_out                      false
% 3.79/0.99  --preprocessed_stats                    false
% 3.79/0.99  
% 3.79/0.99  ------ Abstraction refinement Options
% 3.79/0.99  
% 3.79/0.99  --abstr_ref                             []
% 3.79/0.99  --abstr_ref_prep                        false
% 3.79/0.99  --abstr_ref_until_sat                   false
% 3.79/0.99  --abstr_ref_sig_restrict                funpre
% 3.79/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/0.99  --abstr_ref_under                       []
% 3.79/0.99  
% 3.79/0.99  ------ SAT Options
% 3.79/0.99  
% 3.79/0.99  --sat_mode                              false
% 3.79/0.99  --sat_fm_restart_options                ""
% 3.79/0.99  --sat_gr_def                            false
% 3.79/0.99  --sat_epr_types                         true
% 3.79/0.99  --sat_non_cyclic_types                  false
% 3.79/0.99  --sat_finite_models                     false
% 3.79/0.99  --sat_fm_lemmas                         false
% 3.79/0.99  --sat_fm_prep                           false
% 3.79/0.99  --sat_fm_uc_incr                        true
% 3.79/0.99  --sat_out_model                         small
% 3.79/0.99  --sat_out_clauses                       false
% 3.79/0.99  
% 3.79/0.99  ------ QBF Options
% 3.79/0.99  
% 3.79/0.99  --qbf_mode                              false
% 3.79/0.99  --qbf_elim_univ                         false
% 3.79/0.99  --qbf_dom_inst                          none
% 3.79/0.99  --qbf_dom_pre_inst                      false
% 3.79/0.99  --qbf_sk_in                             false
% 3.79/0.99  --qbf_pred_elim                         true
% 3.79/0.99  --qbf_split                             512
% 3.79/0.99  
% 3.79/0.99  ------ BMC1 Options
% 3.79/0.99  
% 3.79/0.99  --bmc1_incremental                      false
% 3.79/0.99  --bmc1_axioms                           reachable_all
% 3.79/0.99  --bmc1_min_bound                        0
% 3.79/0.99  --bmc1_max_bound                        -1
% 3.79/0.99  --bmc1_max_bound_default                -1
% 3.79/0.99  --bmc1_symbol_reachability              true
% 3.79/0.99  --bmc1_property_lemmas                  false
% 3.79/0.99  --bmc1_k_induction                      false
% 3.79/0.99  --bmc1_non_equiv_states                 false
% 3.79/0.99  --bmc1_deadlock                         false
% 3.79/0.99  --bmc1_ucm                              false
% 3.79/0.99  --bmc1_add_unsat_core                   none
% 3.79/0.99  --bmc1_unsat_core_children              false
% 3.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/0.99  --bmc1_out_stat                         full
% 3.79/0.99  --bmc1_ground_init                      false
% 3.79/0.99  --bmc1_pre_inst_next_state              false
% 3.79/0.99  --bmc1_pre_inst_state                   false
% 3.79/0.99  --bmc1_pre_inst_reach_state             false
% 3.79/0.99  --bmc1_out_unsat_core                   false
% 3.79/0.99  --bmc1_aig_witness_out                  false
% 3.79/0.99  --bmc1_verbose                          false
% 3.79/0.99  --bmc1_dump_clauses_tptp                false
% 3.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.79/0.99  --bmc1_dump_file                        -
% 3.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.79/0.99  --bmc1_ucm_extend_mode                  1
% 3.79/0.99  --bmc1_ucm_init_mode                    2
% 3.79/0.99  --bmc1_ucm_cone_mode                    none
% 3.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.79/0.99  --bmc1_ucm_relax_model                  4
% 3.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/0.99  --bmc1_ucm_layered_model                none
% 3.79/0.99  --bmc1_ucm_max_lemma_size               10
% 3.79/0.99  
% 3.79/0.99  ------ AIG Options
% 3.79/0.99  
% 3.79/0.99  --aig_mode                              false
% 3.79/0.99  
% 3.79/0.99  ------ Instantiation Options
% 3.79/0.99  
% 3.79/0.99  --instantiation_flag                    true
% 3.79/0.99  --inst_sos_flag                         false
% 3.79/0.99  --inst_sos_phase                        true
% 3.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel_side                     num_symb
% 3.79/0.99  --inst_solver_per_active                1400
% 3.79/0.99  --inst_solver_calls_frac                1.
% 3.79/0.99  --inst_passive_queue_type               priority_queues
% 3.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/0.99  --inst_passive_queues_freq              [25;2]
% 3.79/0.99  --inst_dismatching                      true
% 3.79/0.99  --inst_eager_unprocessed_to_passive     true
% 3.79/0.99  --inst_prop_sim_given                   true
% 3.79/0.99  --inst_prop_sim_new                     false
% 3.79/0.99  --inst_subs_new                         false
% 3.79/0.99  --inst_eq_res_simp                      false
% 3.79/0.99  --inst_subs_given                       false
% 3.79/0.99  --inst_orphan_elimination               true
% 3.79/0.99  --inst_learning_loop_flag               true
% 3.79/0.99  --inst_learning_start                   3000
% 3.79/0.99  --inst_learning_factor                  2
% 3.79/0.99  --inst_start_prop_sim_after_learn       3
% 3.79/0.99  --inst_sel_renew                        solver
% 3.79/0.99  --inst_lit_activity_flag                true
% 3.79/0.99  --inst_restr_to_given                   false
% 3.79/0.99  --inst_activity_threshold               500
% 3.79/0.99  --inst_out_proof                        true
% 3.79/0.99  
% 3.79/0.99  ------ Resolution Options
% 3.79/0.99  
% 3.79/0.99  --resolution_flag                       true
% 3.79/0.99  --res_lit_sel                           adaptive
% 3.79/0.99  --res_lit_sel_side                      none
% 3.79/0.99  --res_ordering                          kbo
% 3.79/0.99  --res_to_prop_solver                    active
% 3.79/0.99  --res_prop_simpl_new                    false
% 3.79/0.99  --res_prop_simpl_given                  true
% 3.79/0.99  --res_passive_queue_type                priority_queues
% 3.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/0.99  --res_passive_queues_freq               [15;5]
% 3.79/0.99  --res_forward_subs                      full
% 3.79/0.99  --res_backward_subs                     full
% 3.79/0.99  --res_forward_subs_resolution           true
% 3.79/0.99  --res_backward_subs_resolution          true
% 3.79/0.99  --res_orphan_elimination                true
% 3.79/0.99  --res_time_limit                        2.
% 3.79/0.99  --res_out_proof                         true
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Options
% 3.79/0.99  
% 3.79/0.99  --superposition_flag                    true
% 3.79/0.99  --sup_passive_queue_type                priority_queues
% 3.79/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.79/0.99  --demod_completeness_check              fast
% 3.79/0.99  --demod_use_ground                      true
% 3.79/0.99  --sup_to_prop_solver                    passive
% 3.79/0.99  --sup_prop_simpl_new                    true
% 3.79/0.99  --sup_prop_simpl_given                  true
% 3.79/0.99  --sup_fun_splitting                     false
% 3.79/0.99  --sup_smt_interval                      50000
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Simplification Setup
% 3.79/0.99  
% 3.79/0.99  --sup_indices_passive                   []
% 3.79/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_full_bw                           [BwDemod]
% 3.79/0.99  --sup_immed_triv                        [TrivRules]
% 3.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_immed_bw_main                     []
% 3.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/0.99  
% 3.79/0.99  ------ Combination Options
% 3.79/0.99  
% 3.79/0.99  --comb_res_mult                         3
% 3.79/0.99  --comb_sup_mult                         2
% 3.79/0.99  --comb_inst_mult                        10
% 3.79/0.99  
% 3.79/0.99  ------ Debug Options
% 3.79/0.99  
% 3.79/0.99  --dbg_backtrace                         false
% 3.79/0.99  --dbg_dump_prop_clauses                 false
% 3.79/0.99  --dbg_dump_prop_clauses_file            -
% 3.79/0.99  --dbg_out_stat                          false
% 3.79/0.99  ------ Parsing...
% 3.79/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  ------ Proving...
% 3.79/0.99  ------ Problem Properties 
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  clauses                                 32
% 3.79/0.99  conjectures                             13
% 3.79/0.99  EPR                                     9
% 3.79/0.99  Horn                                    27
% 3.79/0.99  unary                                   12
% 3.79/0.99  binary                                  6
% 3.79/0.99  lits                                    102
% 3.79/0.99  lits eq                                 13
% 3.79/0.99  fd_pure                                 0
% 3.79/0.99  fd_pseudo                               0
% 3.79/0.99  fd_cond                                 3
% 3.79/0.99  fd_pseudo_cond                          1
% 3.79/0.99  AC symbols                              0
% 3.79/0.99  
% 3.79/0.99  ------ Schedule dynamic 5 is on 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  Current options:
% 3.79/0.99  ------ 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options
% 3.79/0.99  
% 3.79/0.99  --out_options                           all
% 3.79/0.99  --tptp_safe_out                         true
% 3.79/0.99  --problem_path                          ""
% 3.79/0.99  --include_path                          ""
% 3.79/0.99  --clausifier                            res/vclausify_rel
% 3.79/0.99  --clausifier_options                    --mode clausify
% 3.79/0.99  --stdin                                 false
% 3.79/0.99  --stats_out                             all
% 3.79/0.99  
% 3.79/0.99  ------ General Options
% 3.79/0.99  
% 3.79/0.99  --fof                                   false
% 3.79/0.99  --time_out_real                         305.
% 3.79/0.99  --time_out_virtual                      -1.
% 3.79/0.99  --symbol_type_check                     false
% 3.79/0.99  --clausify_out                          false
% 3.79/0.99  --sig_cnt_out                           false
% 3.79/0.99  --trig_cnt_out                          false
% 3.79/0.99  --trig_cnt_out_tolerance                1.
% 3.79/0.99  --trig_cnt_out_sk_spl                   false
% 3.79/0.99  --abstr_cl_out                          false
% 3.79/0.99  
% 3.79/0.99  ------ Global Options
% 3.79/0.99  
% 3.79/0.99  --schedule                              default
% 3.79/0.99  --add_important_lit                     false
% 3.79/0.99  --prop_solver_per_cl                    1000
% 3.79/0.99  --min_unsat_core                        false
% 3.79/0.99  --soft_assumptions                      false
% 3.79/0.99  --soft_lemma_size                       3
% 3.79/0.99  --prop_impl_unit_size                   0
% 3.79/0.99  --prop_impl_unit                        []
% 3.79/0.99  --share_sel_clauses                     true
% 3.79/0.99  --reset_solvers                         false
% 3.79/0.99  --bc_imp_inh                            [conj_cone]
% 3.79/0.99  --conj_cone_tolerance                   3.
% 3.79/0.99  --extra_neg_conj                        none
% 3.79/0.99  --large_theory_mode                     true
% 3.79/0.99  --prolific_symb_bound                   200
% 3.79/0.99  --lt_threshold                          2000
% 3.79/0.99  --clause_weak_htbl                      true
% 3.79/0.99  --gc_record_bc_elim                     false
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing Options
% 3.79/0.99  
% 3.79/0.99  --preprocessing_flag                    true
% 3.79/0.99  --time_out_prep_mult                    0.1
% 3.79/0.99  --splitting_mode                        input
% 3.79/0.99  --splitting_grd                         true
% 3.79/0.99  --splitting_cvd                         false
% 3.79/0.99  --splitting_cvd_svl                     false
% 3.79/0.99  --splitting_nvd                         32
% 3.79/0.99  --sub_typing                            true
% 3.79/0.99  --prep_gs_sim                           true
% 3.79/0.99  --prep_unflatten                        true
% 3.79/0.99  --prep_res_sim                          true
% 3.79/0.99  --prep_upred                            true
% 3.79/0.99  --prep_sem_filter                       exhaustive
% 3.79/0.99  --prep_sem_filter_out                   false
% 3.79/0.99  --pred_elim                             true
% 3.79/0.99  --res_sim_input                         true
% 3.79/0.99  --eq_ax_congr_red                       true
% 3.79/0.99  --pure_diseq_elim                       true
% 3.79/0.99  --brand_transform                       false
% 3.79/0.99  --non_eq_to_eq                          false
% 3.79/0.99  --prep_def_merge                        true
% 3.79/0.99  --prep_def_merge_prop_impl              false
% 3.79/0.99  --prep_def_merge_mbd                    true
% 3.79/0.99  --prep_def_merge_tr_red                 false
% 3.79/0.99  --prep_def_merge_tr_cl                  false
% 3.79/0.99  --smt_preprocessing                     true
% 3.79/0.99  --smt_ac_axioms                         fast
% 3.79/0.99  --preprocessed_out                      false
% 3.79/0.99  --preprocessed_stats                    false
% 3.79/0.99  
% 3.79/0.99  ------ Abstraction refinement Options
% 3.79/0.99  
% 3.79/0.99  --abstr_ref                             []
% 3.79/0.99  --abstr_ref_prep                        false
% 3.79/0.99  --abstr_ref_until_sat                   false
% 3.79/0.99  --abstr_ref_sig_restrict                funpre
% 3.79/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/0.99  --abstr_ref_under                       []
% 3.79/0.99  
% 3.79/0.99  ------ SAT Options
% 3.79/0.99  
% 3.79/0.99  --sat_mode                              false
% 3.79/0.99  --sat_fm_restart_options                ""
% 3.79/0.99  --sat_gr_def                            false
% 3.79/0.99  --sat_epr_types                         true
% 3.79/0.99  --sat_non_cyclic_types                  false
% 3.79/0.99  --sat_finite_models                     false
% 3.79/0.99  --sat_fm_lemmas                         false
% 3.79/0.99  --sat_fm_prep                           false
% 3.79/0.99  --sat_fm_uc_incr                        true
% 3.79/0.99  --sat_out_model                         small
% 3.79/0.99  --sat_out_clauses                       false
% 3.79/0.99  
% 3.79/0.99  ------ QBF Options
% 3.79/0.99  
% 3.79/0.99  --qbf_mode                              false
% 3.79/0.99  --qbf_elim_univ                         false
% 3.79/0.99  --qbf_dom_inst                          none
% 3.79/0.99  --qbf_dom_pre_inst                      false
% 3.79/0.99  --qbf_sk_in                             false
% 3.79/0.99  --qbf_pred_elim                         true
% 3.79/0.99  --qbf_split                             512
% 3.79/0.99  
% 3.79/0.99  ------ BMC1 Options
% 3.79/0.99  
% 3.79/0.99  --bmc1_incremental                      false
% 3.79/0.99  --bmc1_axioms                           reachable_all
% 3.79/0.99  --bmc1_min_bound                        0
% 3.79/0.99  --bmc1_max_bound                        -1
% 3.79/0.99  --bmc1_max_bound_default                -1
% 3.79/0.99  --bmc1_symbol_reachability              true
% 3.79/0.99  --bmc1_property_lemmas                  false
% 3.79/0.99  --bmc1_k_induction                      false
% 3.79/0.99  --bmc1_non_equiv_states                 false
% 3.79/0.99  --bmc1_deadlock                         false
% 3.79/0.99  --bmc1_ucm                              false
% 3.79/0.99  --bmc1_add_unsat_core                   none
% 3.79/0.99  --bmc1_unsat_core_children              false
% 3.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/0.99  --bmc1_out_stat                         full
% 3.79/0.99  --bmc1_ground_init                      false
% 3.79/0.99  --bmc1_pre_inst_next_state              false
% 3.79/0.99  --bmc1_pre_inst_state                   false
% 3.79/0.99  --bmc1_pre_inst_reach_state             false
% 3.79/0.99  --bmc1_out_unsat_core                   false
% 3.79/0.99  --bmc1_aig_witness_out                  false
% 3.79/0.99  --bmc1_verbose                          false
% 3.79/0.99  --bmc1_dump_clauses_tptp                false
% 3.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.79/0.99  --bmc1_dump_file                        -
% 3.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.79/0.99  --bmc1_ucm_extend_mode                  1
% 3.79/0.99  --bmc1_ucm_init_mode                    2
% 3.79/0.99  --bmc1_ucm_cone_mode                    none
% 3.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.79/0.99  --bmc1_ucm_relax_model                  4
% 3.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/0.99  --bmc1_ucm_layered_model                none
% 3.79/0.99  --bmc1_ucm_max_lemma_size               10
% 3.79/0.99  
% 3.79/0.99  ------ AIG Options
% 3.79/0.99  
% 3.79/0.99  --aig_mode                              false
% 3.79/0.99  
% 3.79/0.99  ------ Instantiation Options
% 3.79/0.99  
% 3.79/0.99  --instantiation_flag                    true
% 3.79/0.99  --inst_sos_flag                         false
% 3.79/0.99  --inst_sos_phase                        true
% 3.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel_side                     none
% 3.79/0.99  --inst_solver_per_active                1400
% 3.79/0.99  --inst_solver_calls_frac                1.
% 3.79/0.99  --inst_passive_queue_type               priority_queues
% 3.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/0.99  --inst_passive_queues_freq              [25;2]
% 3.79/0.99  --inst_dismatching                      true
% 3.79/0.99  --inst_eager_unprocessed_to_passive     true
% 3.79/0.99  --inst_prop_sim_given                   true
% 3.79/0.99  --inst_prop_sim_new                     false
% 3.79/0.99  --inst_subs_new                         false
% 3.79/0.99  --inst_eq_res_simp                      false
% 3.79/0.99  --inst_subs_given                       false
% 3.79/0.99  --inst_orphan_elimination               true
% 3.79/0.99  --inst_learning_loop_flag               true
% 3.79/0.99  --inst_learning_start                   3000
% 3.79/0.99  --inst_learning_factor                  2
% 3.79/0.99  --inst_start_prop_sim_after_learn       3
% 3.79/0.99  --inst_sel_renew                        solver
% 3.79/0.99  --inst_lit_activity_flag                true
% 3.79/0.99  --inst_restr_to_given                   false
% 3.79/0.99  --inst_activity_threshold               500
% 3.79/0.99  --inst_out_proof                        true
% 3.79/0.99  
% 3.79/0.99  ------ Resolution Options
% 3.79/0.99  
% 3.79/0.99  --resolution_flag                       false
% 3.79/0.99  --res_lit_sel                           adaptive
% 3.79/0.99  --res_lit_sel_side                      none
% 3.79/0.99  --res_ordering                          kbo
% 3.79/0.99  --res_to_prop_solver                    active
% 3.79/0.99  --res_prop_simpl_new                    false
% 3.79/0.99  --res_prop_simpl_given                  true
% 3.79/0.99  --res_passive_queue_type                priority_queues
% 3.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/0.99  --res_passive_queues_freq               [15;5]
% 3.79/0.99  --res_forward_subs                      full
% 3.79/0.99  --res_backward_subs                     full
% 3.79/0.99  --res_forward_subs_resolution           true
% 3.79/0.99  --res_backward_subs_resolution          true
% 3.79/0.99  --res_orphan_elimination                true
% 3.79/0.99  --res_time_limit                        2.
% 3.79/0.99  --res_out_proof                         true
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Options
% 3.79/0.99  
% 3.79/0.99  --superposition_flag                    true
% 3.79/0.99  --sup_passive_queue_type                priority_queues
% 3.79/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.79/0.99  --demod_completeness_check              fast
% 3.79/0.99  --demod_use_ground                      true
% 3.79/0.99  --sup_to_prop_solver                    passive
% 3.79/0.99  --sup_prop_simpl_new                    true
% 3.79/0.99  --sup_prop_simpl_given                  true
% 3.79/0.99  --sup_fun_splitting                     false
% 3.79/0.99  --sup_smt_interval                      50000
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Simplification Setup
% 3.79/0.99  
% 3.79/0.99  --sup_indices_passive                   []
% 3.79/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_full_bw                           [BwDemod]
% 3.79/0.99  --sup_immed_triv                        [TrivRules]
% 3.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_immed_bw_main                     []
% 3.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/0.99  
% 3.79/0.99  ------ Combination Options
% 3.79/0.99  
% 3.79/0.99  --comb_res_mult                         3
% 3.79/0.99  --comb_sup_mult                         2
% 3.79/0.99  --comb_inst_mult                        10
% 3.79/0.99  
% 3.79/0.99  ------ Debug Options
% 3.79/0.99  
% 3.79/0.99  --dbg_backtrace                         false
% 3.79/0.99  --dbg_dump_prop_clauses                 false
% 3.79/0.99  --dbg_dump_prop_clauses_file            -
% 3.79/0.99  --dbg_out_stat                          false
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  % SZS status Theorem for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  fof(f14,conjecture,(
% 3.79/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f15,negated_conjecture,(
% 3.79/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.79/0.99    inference(negated_conjecture,[],[f14])).
% 3.79/0.99  
% 3.79/0.99  fof(f37,plain,(
% 3.79/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f15])).
% 3.79/0.99  
% 3.79/0.99  fof(f38,plain,(
% 3.79/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.79/0.99    inference(flattening,[],[f37])).
% 3.79/0.99  
% 3.79/0.99  fof(f45,plain,(
% 3.79/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.79/0.99    inference(nnf_transformation,[],[f38])).
% 3.79/0.99  
% 3.79/0.99  fof(f46,plain,(
% 3.79/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.79/0.99    inference(flattening,[],[f45])).
% 3.79/0.99  
% 3.79/0.99  fof(f50,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK3 = X2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK3))) )),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f49,plain,(
% 3.79/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f48,plain,(
% 3.79/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,X0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,X0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f47,plain,(
% 3.79/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f51,plain,(
% 3.79/0.99    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f50,f49,f48,f47])).
% 3.79/0.99  
% 3.79/0.99  fof(f83,plain,(
% 3.79/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.79/0.99    inference(cnf_transformation,[],[f51])).
% 3.79/0.99  
% 3.79/0.99  fof(f87,plain,(
% 3.79/0.99    sK2 = sK3),
% 3.79/0.99    inference(cnf_transformation,[],[f51])).
% 3.79/0.99  
% 3.79/0.99  fof(f6,axiom,(
% 3.79/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f23,plain,(
% 3.79/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.79/0.99    inference(ennf_transformation,[],[f6])).
% 3.79/0.99  
% 3.79/0.99  fof(f24,plain,(
% 3.79/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.79/0.99    inference(flattening,[],[f23])).
% 3.79/0.99  
% 3.79/0.99  fof(f60,plain,(
% 3.79/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f24])).
% 3.79/0.99  
% 3.79/0.99  fof(f82,plain,(
% 3.79/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.79/0.99    inference(cnf_transformation,[],[f51])).
% 3.79/0.99  
% 3.79/0.99  fof(f7,axiom,(
% 3.79/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f25,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/0.99    inference(ennf_transformation,[],[f7])).
% 3.79/0.99  
% 3.79/0.99  fof(f26,plain,(
% 3.79/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/0.99    inference(flattening,[],[f25])).
% 3.79/0.99  
% 3.79/0.99  fof(f42,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/0.99    inference(nnf_transformation,[],[f26])).
% 3.79/0.99  
% 3.79/0.99  fof(f61,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f42])).
% 3.79/0.99  
% 3.79/0.99  fof(f5,axiom,(
% 3.79/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f22,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/0.99    inference(ennf_transformation,[],[f5])).
% 3.79/0.99  
% 3.79/0.99  fof(f59,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f22])).
% 3.79/0.99  
% 3.79/0.99  fof(f65,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f42])).
% 3.79/0.99  
% 3.79/0.99  fof(f94,plain,(
% 3.79/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.79/0.99    inference(equality_resolution,[],[f65])).
% 3.79/0.99  
% 3.79/0.99  fof(f84,plain,(
% 3.79/0.99    v1_funct_1(sK3)),
% 3.79/0.99    inference(cnf_transformation,[],[f51])).
% 3.79/0.99  
% 3.79/0.99  fof(f86,plain,(
% 3.79/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.79/0.99    inference(cnf_transformation,[],[f51])).
% 3.79/0.99  
% 3.79/0.99  fof(f1,axiom,(
% 3.79/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f39,plain,(
% 3.79/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.79/0.99    inference(nnf_transformation,[],[f1])).
% 3.79/0.99  
% 3.79/0.99  fof(f40,plain,(
% 3.79/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.79/0.99    inference(flattening,[],[f39])).
% 3.79/0.99  
% 3.79/0.99  fof(f53,plain,(
% 3.79/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.79/0.99    inference(cnf_transformation,[],[f40])).
% 3.79/0.99  
% 3.79/0.99  fof(f90,plain,(
% 3.79/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.79/0.99    inference(equality_resolution,[],[f53])).
% 3.79/0.99  
% 3.79/0.99  fof(f8,axiom,(
% 3.79/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f27,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.79/0.99    inference(ennf_transformation,[],[f8])).
% 3.79/0.99  
% 3.79/0.99  fof(f28,plain,(
% 3.79/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.79/0.99    inference(flattening,[],[f27])).
% 3.79/0.99  
% 3.79/0.99  fof(f68,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f28])).
% 3.79/0.99  
% 3.79/0.99  fof(f12,axiom,(
% 3.79/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f33,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f12])).
% 3.79/0.99  
% 3.79/0.99  fof(f34,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.79/0.99    inference(flattening,[],[f33])).
% 3.79/0.99  
% 3.79/0.99  fof(f43,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.79/0.99    inference(nnf_transformation,[],[f34])).
% 3.79/0.99  
% 3.79/0.99  fof(f74,plain,(
% 3.79/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f43])).
% 3.79/0.99  
% 3.79/0.99  fof(f97,plain,(
% 3.79/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.79/0.99    inference(equality_resolution,[],[f74])).
% 3.79/0.99  
% 3.79/0.99  fof(f4,axiom,(
% 3.79/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f18,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.79/0.99    inference(pure_predicate_removal,[],[f4])).
% 3.79/0.99  
% 3.79/0.99  fof(f21,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/0.99    inference(ennf_transformation,[],[f18])).
% 3.79/0.99  
% 3.79/0.99  fof(f58,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f21])).
% 3.79/0.99  
% 3.79/0.99  fof(f2,axiom,(
% 3.79/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f19,plain,(
% 3.79/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.79/0.99    inference(ennf_transformation,[],[f2])).
% 3.79/0.99  
% 3.79/0.99  fof(f41,plain,(
% 3.79/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.79/0.99    inference(nnf_transformation,[],[f19])).
% 3.79/0.99  
% 3.79/0.99  fof(f55,plain,(
% 3.79/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f41])).
% 3.79/0.99  
% 3.79/0.99  fof(f3,axiom,(
% 3.79/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f20,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/0.99    inference(ennf_transformation,[],[f3])).
% 3.79/0.99  
% 3.79/0.99  fof(f57,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f20])).
% 3.79/0.99  
% 3.79/0.99  fof(f73,plain,(
% 3.79/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f43])).
% 3.79/0.99  
% 3.79/0.99  fof(f98,plain,(
% 3.79/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.79/0.99    inference(equality_resolution,[],[f73])).
% 3.79/0.99  
% 3.79/0.99  fof(f77,plain,(
% 3.79/0.99    v2_pre_topc(sK0)),
% 3.79/0.99    inference(cnf_transformation,[],[f51])).
% 3.79/0.99  
% 3.79/0.99  fof(f78,plain,(
% 3.79/0.99    l1_pre_topc(sK0)),
% 3.79/0.99    inference(cnf_transformation,[],[f51])).
% 3.79/0.99  
% 3.79/0.99  fof(f79,plain,(
% 3.79/0.99    v2_pre_topc(sK1)),
% 3.79/0.99    inference(cnf_transformation,[],[f51])).
% 3.79/0.99  
% 3.79/0.99  fof(f80,plain,(
% 3.79/0.99    l1_pre_topc(sK1)),
% 3.79/0.99    inference(cnf_transformation,[],[f51])).
% 3.79/0.99  
% 3.79/0.99  fof(f85,plain,(
% 3.79/0.99    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.79/0.99    inference(cnf_transformation,[],[f51])).
% 3.79/0.99  
% 3.79/0.99  fof(f89,plain,(
% 3.79/0.99    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 3.79/0.99    inference(cnf_transformation,[],[f51])).
% 3.79/0.99  
% 3.79/0.99  fof(f88,plain,(
% 3.79/0.99    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 3.79/0.99    inference(cnf_transformation,[],[f51])).
% 3.79/0.99  
% 3.79/0.99  fof(f10,axiom,(
% 3.79/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f30,plain,(
% 3.79/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.79/0.99    inference(ennf_transformation,[],[f10])).
% 3.79/0.99  
% 3.79/0.99  fof(f71,plain,(
% 3.79/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f30])).
% 3.79/0.99  
% 3.79/0.99  fof(f11,axiom,(
% 3.79/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f16,plain,(
% 3.79/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 3.79/0.99    inference(pure_predicate_removal,[],[f11])).
% 3.79/0.99  
% 3.79/0.99  fof(f31,plain,(
% 3.79/0.99    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f16])).
% 3.79/0.99  
% 3.79/0.99  fof(f32,plain,(
% 3.79/0.99    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.79/0.99    inference(flattening,[],[f31])).
% 3.79/0.99  
% 3.79/0.99  fof(f72,plain,(
% 3.79/0.99    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f32])).
% 3.79/0.99  
% 3.79/0.99  fof(f9,axiom,(
% 3.79/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f17,plain,(
% 3.79/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 3.79/0.99    inference(pure_predicate_removal,[],[f9])).
% 3.79/0.99  
% 3.79/0.99  fof(f29,plain,(
% 3.79/0.99    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.79/0.99    inference(ennf_transformation,[],[f17])).
% 3.79/0.99  
% 3.79/0.99  fof(f70,plain,(
% 3.79/0.99    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f29])).
% 3.79/0.99  
% 3.79/0.99  fof(f13,axiom,(
% 3.79/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f35,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f13])).
% 3.79/0.99  
% 3.79/0.99  fof(f36,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.79/0.99    inference(flattening,[],[f35])).
% 3.79/0.99  
% 3.79/0.99  fof(f44,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.79/0.99    inference(nnf_transformation,[],[f36])).
% 3.79/0.99  
% 3.79/0.99  fof(f76,plain,(
% 3.79/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f44])).
% 3.79/0.99  
% 3.79/0.99  fof(f99,plain,(
% 3.79/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.79/0.99    inference(equality_resolution,[],[f76])).
% 3.79/0.99  
% 3.79/0.99  fof(f75,plain,(
% 3.79/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f44])).
% 3.79/0.99  
% 3.79/0.99  fof(f100,plain,(
% 3.79/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.79/0.99    inference(equality_resolution,[],[f75])).
% 3.79/0.99  
% 3.79/0.99  fof(f52,plain,(
% 3.79/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.79/0.99    inference(cnf_transformation,[],[f40])).
% 3.79/0.99  
% 3.79/0.99  fof(f91,plain,(
% 3.79/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.79/0.99    inference(equality_resolution,[],[f52])).
% 3.79/0.99  
% 3.79/0.99  fof(f54,plain,(
% 3.79/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f40])).
% 3.79/0.99  
% 3.79/0.99  fof(f63,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f42])).
% 3.79/0.99  
% 3.79/0.99  cnf(c_31,negated_conjecture,
% 3.79/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.79/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2343,plain,
% 3.79/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_27,negated_conjecture,
% 3.79/0.99      ( sK2 = sK3 ),
% 3.79/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2385,plain,
% 3.79/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.79/0.99      inference(light_normalisation,[status(thm)],[c_2343,c_27]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_8,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.79/0.99      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 3.79/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2363,plain,
% 3.79/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.79/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 3.79/0.99      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4298,plain,
% 3.79/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) = iProver_top
% 3.79/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_2385,c_2363]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_32,negated_conjecture,
% 3.79/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2342,plain,
% 3.79/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2382,plain,
% 3.79/0.99      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.79/0.99      inference(light_normalisation,[status(thm)],[c_2342,c_27]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_14,plain,
% 3.79/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.79/0.99      | k1_xboole_0 = X2 ),
% 3.79/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2357,plain,
% 3.79/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.79/0.99      | k1_xboole_0 = X1
% 3.79/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.79/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4402,plain,
% 3.79/0.99      ( k1_relset_1(X0,u1_struct_0(sK1),sK3) = X0
% 3.79/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 3.79/0.99      | v1_funct_2(sK3,X0,u1_struct_0(sK1)) != iProver_top
% 3.79/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_4298,c_2357]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5576,plain,
% 3.79/0.99      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = u1_struct_0(sK0)
% 3.79/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 3.79/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_2382,c_4402]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_7,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2364,plain,
% 3.79/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.79/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3732,plain,
% 3.79/0.99      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_2385,c_2364]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5581,plain,
% 3.79/0.99      ( u1_struct_0(sK1) = k1_xboole_0
% 3.79/0.99      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.79/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top ),
% 3.79/0.99      inference(light_normalisation,[status(thm)],[c_5576,c_3732]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4401,plain,
% 3.79/0.99      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = u1_struct_0(sK0)
% 3.79/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_2385,c_2357]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4414,plain,
% 3.79/0.99      ( u1_struct_0(sK1) = k1_xboole_0
% 3.79/0.99      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 3.79/0.99      inference(light_normalisation,[status(thm)],[c_4401,c_3732]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6120,plain,
% 3.79/0.99      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.79/0.99      | u1_struct_0(sK1) = k1_xboole_0 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_5581,c_2382,c_4414]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6121,plain,
% 3.79/0.99      ( u1_struct_0(sK1) = k1_xboole_0
% 3.79/0.99      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_6120]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6168,plain,
% 3.79/0.99      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) = iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_6121,c_2385]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_10,plain,
% 3.79/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.79/0.99      | k1_xboole_0 = X1
% 3.79/0.99      | k1_xboole_0 = X0 ),
% 3.79/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2361,plain,
% 3.79/0.99      ( k1_xboole_0 = X0
% 3.79/0.99      | k1_xboole_0 = X1
% 3.79/0.99      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 3.79/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6830,plain,
% 3.79/0.99      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.79/0.99      | u1_struct_0(sK0) = k1_xboole_0
% 3.79/0.99      | sK3 = k1_xboole_0
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_6168,c_2361]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6169,plain,
% 3.79/0.99      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) = iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_6121,c_2382]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_7607,plain,
% 3.79/0.99      ( sK3 = k1_xboole_0
% 3.79/0.99      | u1_struct_0(sK0) = k1_xboole_0
% 3.79/0.99      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_6830,c_6169]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_7608,plain,
% 3.79/0.99      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.79/0.99      | u1_struct_0(sK0) = k1_xboole_0
% 3.79/0.99      | sK3 = k1_xboole_0 ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_7607]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_7653,plain,
% 3.79/0.99      ( u1_struct_0(sK0) = k1_xboole_0
% 3.79/0.99      | sK3 = k1_xboole_0
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_7608,c_2385]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_30,negated_conjecture,
% 3.79/0.99      ( v1_funct_1(sK3) ),
% 3.79/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_45,plain,
% 3.79/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_28,negated_conjecture,
% 3.79/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
% 3.79/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_47,plain,
% 3.79/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2707,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
% 3.79/0.99      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3320,plain,
% 3.79/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.79/0.99      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2707]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3321,plain,
% 3.79/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top
% 3.79/0.99      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_3320]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1,plain,
% 3.79/0.99      ( r1_tarski(X0,X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2708,plain,
% 3.79/0.99      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3565,plain,
% 3.79/0.99      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2708]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3566,plain,
% 3.79/0.99      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_3565]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4997,plain,
% 3.79/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.79/0.99      | k1_relset_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_16,plain,
% 3.79/0.99      ( v1_funct_2(X0,X1,X2)
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/0.99      | ~ v1_funct_1(X0)
% 3.79/0.99      | k1_relset_1(X1,X2,X0) != X1 ),
% 3.79/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2736,plain,
% 3.79/0.99      ( v1_funct_2(sK3,X0,X1)
% 3.79/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.79/0.99      | ~ v1_funct_1(sK3)
% 3.79/0.99      | k1_relset_1(X0,X1,sK3) != X0 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5007,plain,
% 3.79/0.99      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.79/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.79/0.99      | ~ v1_funct_1(sK3)
% 3.79/0.99      | k1_relset_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) != k1_relat_1(sK3) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2736]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5008,plain,
% 3.79/0.99      ( k1_relset_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) != k1_relat_1(sK3)
% 3.79/0.99      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.79/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_5007]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2346,plain,
% 3.79/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_21,plain,
% 3.79/0.99      ( v5_pre_topc(X0,X1,X2)
% 3.79/0.99      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 3.79/0.99      | ~ v2_pre_topc(X1)
% 3.79/0.99      | ~ v2_pre_topc(X2)
% 3.79/0.99      | ~ l1_pre_topc(X1)
% 3.79/0.99      | ~ l1_pre_topc(X2)
% 3.79/0.99      | ~ v1_funct_1(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2352,plain,
% 3.79/0.99      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 3.79/0.99      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 3.79/0.99      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.79/0.99      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 3.79/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.79/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 3.79/0.99      | v2_pre_topc(X1) != iProver_top
% 3.79/0.99      | v2_pre_topc(X2) != iProver_top
% 3.79/0.99      | l1_pre_topc(X1) != iProver_top
% 3.79/0.99      | l1_pre_topc(X2) != iProver_top
% 3.79/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5150,plain,
% 3.79/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.79/0.99      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.79/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.79/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.79/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.79/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.79/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_2346,c_2352]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/0.99      | v4_relat_1(X0,X1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4,plain,
% 3.79/0.99      ( ~ v4_relat_1(X0,X1)
% 3.79/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.79/0.99      | ~ v1_relat_1(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_493,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.79/0.99      | ~ v1_relat_1(X0) ),
% 3.79/0.99      inference(resolution,[status(thm)],[c_6,c_4]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/0.99      | v1_relat_1(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_497,plain,
% 3.79/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_493,c_5]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_498,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/0.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_497]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2336,plain,
% 3.79/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.79/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_498]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2816,plain,
% 3.79/0.99      ( r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_2385,c_2336]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4297,plain,
% 3.79/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top
% 3.79/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_2346,c_2363]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_22,plain,
% 3.79/0.99      ( ~ v5_pre_topc(X0,X1,X2)
% 3.79/0.99      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 3.79/0.99      | ~ v2_pre_topc(X1)
% 3.79/0.99      | ~ v2_pre_topc(X2)
% 3.79/0.99      | ~ l1_pre_topc(X1)
% 3.79/0.99      | ~ l1_pre_topc(X2)
% 3.79/0.99      | ~ v1_funct_1(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2351,plain,
% 3.79/0.99      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.79/0.99      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 3.79/0.99      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.79/0.99      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 3.79/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.79/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 3.79/0.99      | v2_pre_topc(X1) != iProver_top
% 3.79/0.99      | v2_pre_topc(X2) != iProver_top
% 3.79/0.99      | l1_pre_topc(X1) != iProver_top
% 3.79/0.99      | l1_pre_topc(X2) != iProver_top
% 3.79/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5064,plain,
% 3.79/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.79/0.99      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.79/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.79/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.79/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.79/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.79/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_2346,c_2351]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_37,negated_conjecture,
% 3.79/0.99      ( v2_pre_topc(sK0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_38,plain,
% 3.79/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_36,negated_conjecture,
% 3.79/0.99      ( l1_pre_topc(sK0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_39,plain,
% 3.79/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_35,negated_conjecture,
% 3.79/0.99      ( v2_pre_topc(sK1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_40,plain,
% 3.79/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_34,negated_conjecture,
% 3.79/0.99      ( l1_pre_topc(sK1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_41,plain,
% 3.79/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_29,negated_conjecture,
% 3.79/0.99      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
% 3.79/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_46,plain,
% 3.79/0.99      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_25,negated_conjecture,
% 3.79/0.99      ( ~ v5_pre_topc(sK2,sK0,sK1)
% 3.79/0.99      | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.79/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2348,plain,
% 3.79/0.99      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
% 3.79/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2431,plain,
% 3.79/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.79/0.99      | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
% 3.79/0.99      inference(light_normalisation,[status(thm)],[c_2348,c_27]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_26,negated_conjecture,
% 3.79/0.99      ( v5_pre_topc(sK2,sK0,sK1)
% 3.79/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.79/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2347,plain,
% 3.79/0.99      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
% 3.79/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2426,plain,
% 3.79/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.79/0.99      | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
% 3.79/0.99      inference(light_normalisation,[status(thm)],[c_2347,c_27]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_19,plain,
% 3.79/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.79/0.99      | ~ l1_pre_topc(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2645,plain,
% 3.79/0.99      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.79/0.99      | ~ l1_pre_topc(sK1) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2646,plain,
% 3.79/0.99      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 3.79/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2645]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_20,plain,
% 3.79/0.99      ( ~ v2_pre_topc(X0)
% 3.79/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.79/0.99      | ~ l1_pre_topc(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2651,plain,
% 3.79/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.79/0.99      | ~ v2_pre_topc(sK1)
% 3.79/0.99      | ~ l1_pre_topc(sK1) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2652,plain,
% 3.79/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.79/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.79/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2651]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_18,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.79/0.99      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2797,plain,
% 3.79/0.99      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.79/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2798,plain,
% 3.79/0.99      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.79/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2797]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_23,plain,
% 3.79/0.99      ( v5_pre_topc(X0,X1,X2)
% 3.79/0.99      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 3.79/0.99      | ~ v2_pre_topc(X1)
% 3.79/0.99      | ~ v2_pre_topc(X2)
% 3.79/0.99      | ~ l1_pre_topc(X1)
% 3.79/0.99      | ~ l1_pre_topc(X2)
% 3.79/0.99      | ~ v1_funct_1(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2782,plain,
% 3.79/0.99      ( v5_pre_topc(X0,sK0,X1)
% 3.79/0.99      | ~ v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 3.79/0.99      | ~ v2_pre_topc(X1)
% 3.79/0.99      | ~ v2_pre_topc(sK0)
% 3.79/0.99      | ~ l1_pre_topc(X1)
% 3.79/0.99      | ~ l1_pre_topc(sK0)
% 3.79/0.99      | ~ v1_funct_1(X0) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3229,plain,
% 3.79/0.99      ( ~ v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.79/0.99      | v5_pre_topc(X0,sK0,sK1)
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.79/0.99      | ~ v2_pre_topc(sK1)
% 3.79/0.99      | ~ v2_pre_topc(sK0)
% 3.79/0.99      | ~ l1_pre_topc(sK1)
% 3.79/0.99      | ~ l1_pre_topc(sK0)
% 3.79/0.99      | ~ v1_funct_1(X0) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2782]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3719,plain,
% 3.79/0.99      ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.79/0.99      | v5_pre_topc(sK3,sK0,sK1)
% 3.79/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.79/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.79/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.79/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.79/0.99      | ~ v2_pre_topc(sK1)
% 3.79/0.99      | ~ v2_pre_topc(sK0)
% 3.79/0.99      | ~ l1_pre_topc(sK1)
% 3.79/0.99      | ~ l1_pre_topc(sK0)
% 3.79/0.99      | ~ v1_funct_1(sK3) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_3229]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3720,plain,
% 3.79/0.99      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.79/0.99      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.79/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.79/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.79/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.79/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.79/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_3719]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_24,plain,
% 3.79/0.99      ( ~ v5_pre_topc(X0,X1,X2)
% 3.79/0.99      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 3.79/0.99      | ~ v2_pre_topc(X1)
% 3.79/0.99      | ~ v2_pre_topc(X2)
% 3.79/0.99      | ~ l1_pre_topc(X1)
% 3.79/0.99      | ~ l1_pre_topc(X2)
% 3.79/0.99      | ~ v1_funct_1(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2792,plain,
% 3.79/0.99      ( ~ v5_pre_topc(X0,sK0,X1)
% 3.79/0.99      | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 3.79/0.99      | ~ v2_pre_topc(X1)
% 3.79/0.99      | ~ v2_pre_topc(sK0)
% 3.79/0.99      | ~ l1_pre_topc(X1)
% 3.79/0.99      | ~ l1_pre_topc(sK0)
% 3.79/0.99      | ~ v1_funct_1(X0) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_24]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3269,plain,
% 3.79/0.99      ( v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.79/0.99      | ~ v5_pre_topc(X0,sK0,sK1)
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.79/0.99      | ~ v2_pre_topc(sK1)
% 3.79/0.99      | ~ v2_pre_topc(sK0)
% 3.79/0.99      | ~ l1_pre_topc(sK1)
% 3.79/0.99      | ~ l1_pre_topc(sK0)
% 3.79/0.99      | ~ v1_funct_1(X0) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2792]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3755,plain,
% 3.79/0.99      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.79/0.99      | ~ v5_pre_topc(sK3,sK0,sK1)
% 3.79/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.79/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.79/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.79/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.79/0.99      | ~ v2_pre_topc(sK1)
% 3.79/0.99      | ~ v2_pre_topc(sK0)
% 3.79/0.99      | ~ l1_pre_topc(sK1)
% 3.79/0.99      | ~ l1_pre_topc(sK0)
% 3.79/0.99      | ~ v1_funct_1(sK3) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_3269]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3756,plain,
% 3.79/0.99      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.79/0.99      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.79/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.79/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.79/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.79/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.79/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_3755]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5299,plain,
% 3.79/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.79/0.99      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_5064,c_38,c_39,c_40,c_41,c_45,c_46,c_2431,c_2385,
% 3.79/0.99                 c_2426,c_2382,c_2646,c_2652,c_2798,c_3720,c_3756,c_5150]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5300,plain,
% 3.79/0.99      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_5299]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5303,plain,
% 3.79/0.99      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_5300,c_38,c_39,c_40,c_41,c_45,c_46,c_2385,c_2426,
% 3.79/0.99                 c_2382,c_2646,c_2652,c_2798,c_3756,c_5150]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5309,plain,
% 3.79/0.99      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.79/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_4297,c_5303]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5367,plain,
% 3.79/0.99      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_5150,c_2816,c_5309]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_7638,plain,
% 3.79/0.99      ( u1_struct_0(sK0) = k1_xboole_0
% 3.79/0.99      | sK3 = k1_xboole_0
% 3.79/0.99      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_7608,c_5367]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_8001,plain,
% 3.79/0.99      ( sK3 = k1_xboole_0 | u1_struct_0(sK0) = k1_xboole_0 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_7653,c_45,c_28,c_47,c_3320,c_3321,c_3565,c_3566,
% 3.79/0.99                 c_4997,c_5008,c_7638]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_8002,plain,
% 3.79/0.99      ( u1_struct_0(sK0) = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_8001]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3127,plain,
% 3.79/0.99      ( r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_2346,c_2336]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4350,plain,
% 3.79/0.99      ( k1_relset_1(X0,u1_struct_0(sK1),sK3) = k1_relat_1(sK3)
% 3.79/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_4298,c_2364]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4966,plain,
% 3.79/0.99      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_3127,c_4350]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2356,plain,
% 3.79/0.99      ( k1_relset_1(X0,X1,X2) != X0
% 3.79/0.99      | v1_funct_2(X2,X0,X1) = iProver_top
% 3.79/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.79/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4973,plain,
% 3.79/0.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3)
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) = iProver_top
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.79/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_4966,c_2356]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2691,plain,
% 3.79/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.79/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_498]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2692,plain,
% 3.79/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.79/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2691]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2350,plain,
% 3.79/0.99      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 3.79/0.99      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 3.79/0.99      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.79/0.99      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 3.79/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.79/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 3.79/0.99      | v2_pre_topc(X1) != iProver_top
% 3.79/0.99      | v2_pre_topc(X2) != iProver_top
% 3.79/0.99      | l1_pre_topc(X1) != iProver_top
% 3.79/0.99      | l1_pre_topc(X2) != iProver_top
% 3.79/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4388,plain,
% 3.79/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.79/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.79/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.79/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.79/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.79/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.79/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.79/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.79/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_2346,c_2350]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2648,plain,
% 3.79/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.79/0.99      | ~ l1_pre_topc(sK0) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2649,plain,
% 3.79/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 3.79/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2648]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2654,plain,
% 3.79/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.79/0.99      | ~ v2_pre_topc(sK0)
% 3.79/0.99      | ~ l1_pre_topc(sK0) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2655,plain,
% 3.79/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.79/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.79/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2654]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2805,plain,
% 3.79/0.99      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.79/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2806,plain,
% 3.79/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.79/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2805]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2772,plain,
% 3.79/0.99      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
% 3.79/0.99      | ~ v5_pre_topc(X0,sK0,X1)
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.79/0.99      | ~ v2_pre_topc(X1)
% 3.79/0.99      | ~ v2_pre_topc(sK0)
% 3.79/0.99      | ~ l1_pre_topc(X1)
% 3.79/0.99      | ~ l1_pre_topc(sK0)
% 3.79/0.99      | ~ v1_funct_1(X0) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3189,plain,
% 3.79/0.99      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.79/0.99      | ~ v5_pre_topc(X0,sK0,sK1)
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 3.79/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.79/0.99      | ~ v2_pre_topc(sK1)
% 3.79/0.99      | ~ v2_pre_topc(sK0)
% 3.79/1.00      | ~ l1_pre_topc(sK1)
% 3.79/1.00      | ~ l1_pre_topc(sK0)
% 3.79/1.00      | ~ v1_funct_1(X0) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_2772]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3695,plain,
% 3.79/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.79/1.00      | ~ v5_pre_topc(sK3,sK0,sK1)
% 3.79/1.00      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 3.79/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.79/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 3.79/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.79/1.00      | ~ v2_pre_topc(sK1)
% 3.79/1.00      | ~ v2_pre_topc(sK0)
% 3.79/1.00      | ~ l1_pre_topc(sK1)
% 3.79/1.00      | ~ l1_pre_topc(sK0)
% 3.79/1.00      | ~ v1_funct_1(sK3) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_3189]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3696,plain,
% 3.79/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 3.79/1.00      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.79/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.79/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.79/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.79/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.79/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_3695]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2349,plain,
% 3.79/1.00      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.79/1.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 3.79/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.79/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 3.79/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.79/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 3.79/1.00      | v2_pre_topc(X1) != iProver_top
% 3.79/1.00      | v2_pre_topc(X2) != iProver_top
% 3.79/1.00      | l1_pre_topc(X1) != iProver_top
% 3.79/1.00      | l1_pre_topc(X2) != iProver_top
% 3.79/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3810,plain,
% 3.79/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.79/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.79/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.79/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.79/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.79/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.79/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2346,c_2349]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2762,plain,
% 3.79/1.00      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
% 3.79/1.00      | v5_pre_topc(X0,sK0,X1)
% 3.79/1.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
% 3.79/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.79/1.00      | ~ v2_pre_topc(X1)
% 3.79/1.00      | ~ v2_pre_topc(sK0)
% 3.79/1.00      | ~ l1_pre_topc(X1)
% 3.79/1.00      | ~ l1_pre_topc(sK0)
% 3.79/1.00      | ~ v1_funct_1(X0) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3149,plain,
% 3.79/1.00      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.79/1.00      | v5_pre_topc(X0,sK0,sK1)
% 3.79/1.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 3.79/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.79/1.00      | ~ v2_pre_topc(sK1)
% 3.79/1.00      | ~ v2_pre_topc(sK0)
% 3.79/1.00      | ~ l1_pre_topc(sK1)
% 3.79/1.00      | ~ l1_pre_topc(sK0)
% 3.79/1.00      | ~ v1_funct_1(X0) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_2762]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3671,plain,
% 3.79/1.00      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.79/1.00      | v5_pre_topc(sK3,sK0,sK1)
% 3.79/1.00      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 3.79/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.79/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 3.79/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.79/1.00      | ~ v2_pre_topc(sK1)
% 3.79/1.00      | ~ v2_pre_topc(sK0)
% 3.79/1.00      | ~ l1_pre_topc(sK1)
% 3.79/1.00      | ~ l1_pre_topc(sK0)
% 3.79/1.00      | ~ v1_funct_1(sK3) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_3149]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3672,plain,
% 3.79/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.79/1.00      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.79/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.79/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.79/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.79/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.79/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_3671]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4198,plain,
% 3.79/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.79/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_3810,c_38,c_39,c_40,c_41,c_45,c_46,c_2431,c_2385,
% 3.79/1.00                 c_2382,c_2649,c_2655,c_2806,c_3672]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4199,plain,
% 3.79/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_4198]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4954,plain,
% 3.79/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_4388,c_38,c_39,c_40,c_41,c_45,c_46,c_2385,c_2426,
% 3.79/1.00                 c_2382,c_2649,c_2655,c_2806,c_3696,c_4199]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4955,plain,
% 3.79/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_4954]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4960,plain,
% 3.79/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.79/1.00      | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_4298,c_4955]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9513,plain,
% 3.79/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.79/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3) ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_4973,c_45,c_47,c_2692,c_4960]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9514,plain,
% 3.79/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3)
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_9513]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9519,plain,
% 3.79/1.00      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) != k1_relat_1(sK3)
% 3.79/1.00      | sK3 = k1_xboole_0
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_8002,c_9514]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2,plain,
% 3.79/1.00      ( r1_tarski(X0,X0) ),
% 3.79/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_111,plain,
% 3.79/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_0,plain,
% 3.79/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.79/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_115,plain,
% 3.79/1.00      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.79/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1580,plain,( X0 = X0 ),theory(equality) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3040,plain,
% 3.79/1.00      ( sK3 = sK3 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1580]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1581,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3618,plain,
% 3.79/1.00      ( X0 != X1
% 3.79/1.00      | X0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.79/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != X1 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1581]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3619,plain,
% 3.79/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != k1_xboole_0
% 3.79/1.00      | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.79/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_3618]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1587,plain,
% 3.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.79/1.00      | v1_funct_2(X3,X4,X5)
% 3.79/1.00      | X3 != X0
% 3.79/1.00      | X4 != X1
% 3.79/1.00      | X5 != X2 ),
% 3.79/1.00      theory(equality) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2742,plain,
% 3.79/1.00      ( v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.79/1.00      | X2 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.79/1.00      | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.79/1.00      | X0 != sK3 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1587]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3774,plain,
% 3.79/1.00      ( v1_funct_2(sK3,X0,X1)
% 3.79/1.00      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.79/1.00      | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.79/1.00      | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.79/1.00      | sK3 != sK3 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_2742]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3777,plain,
% 3.79/1.00      ( X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.79/1.00      | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.79/1.00      | sK3 != sK3
% 3.79/1.00      | v1_funct_2(sK3,X1,X0) = iProver_top
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_3774]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3779,plain,
% 3.79/1.00      ( sK3 != sK3
% 3.79/1.00      | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.79/1.00      | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.79/1.00      | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_3777]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5511,plain,
% 3.79/1.00      ( X0 != X1
% 3.79/1.00      | X0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.79/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != X1 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1581]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5512,plain,
% 3.79/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_xboole_0
% 3.79/1.00      | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.79/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_5511]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4400,plain,
% 3.79/1.00      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.79/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2346,c_2357]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3731,plain,
% 3.79/1.00      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2346,c_2364]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4421,plain,
% 3.79/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 3.79/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.79/1.00      inference(light_normalisation,[status(thm)],[c_4400,c_3731]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4427,plain,
% 3.79/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.79/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 3.79/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.79/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4421]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_8456,plain,
% 3.79/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.79/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0 ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_4421,c_29,c_4427]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_8457,plain,
% 3.79/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 3.79/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.79/1.00      inference(renaming,[status(thm)],[c_8456]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2345,plain,
% 3.79/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_8499,plain,
% 3.79/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_8457,c_2345]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_8498,plain,
% 3.79/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) = iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_8457,c_2346]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9457,plain,
% 3.79/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.79/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
% 3.79/1.00      | sK3 = k1_xboole_0
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_8498,c_2361]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_8033,plain,
% 3.79/1.00      ( sK3 = k1_xboole_0
% 3.79/1.00      | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_8002,c_5367]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9577,plain,
% 3.79/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.79/1.00      | sK3 = k1_xboole_0
% 3.79/1.00      | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_8457,c_8033]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9630,plain,
% 3.79/1.00      ( sK3 = k1_xboole_0
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_9519,c_46,c_111,c_115,c_3040,c_3619,c_3779,c_5512,
% 3.79/1.00                 c_8457,c_8499,c_9457,c_9514,c_9577]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9636,plain,
% 3.79/1.00      ( sK3 = k1_xboole_0
% 3.79/1.00      | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_4298,c_9630]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9817,plain,
% 3.79/1.00      ( sK3 = k1_xboole_0 ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_9636,c_47,c_2692]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2366,plain,
% 3.79/1.00      ( X0 = X1
% 3.79/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.79/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3818,plain,
% 3.79/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.79/1.00      | r1_tarski(u1_struct_0(sK0),k1_relat_1(sK3)) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2816,c_2366]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9864,plain,
% 3.79/1.00      ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
% 3.79/1.00      | r1_tarski(u1_struct_0(sK0),k1_relat_1(k1_xboole_0)) != iProver_top ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_9817,c_3818]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2365,plain,
% 3.79/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4965,plain,
% 3.79/1.00      ( k1_relset_1(k1_relat_1(sK3),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2365,c_4350]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_12,plain,
% 3.79/1.00      ( v1_funct_2(X0,X1,X2)
% 3.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.79/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.79/1.00      | k1_xboole_0 = X2 ),
% 3.79/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2359,plain,
% 3.79/1.00      ( k1_relset_1(X0,X1,X2) != X0
% 3.79/1.00      | k1_xboole_0 = X1
% 3.79/1.00      | v1_funct_2(X2,X0,X1) = iProver_top
% 3.79/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5242,plain,
% 3.79/1.00      ( u1_struct_0(sK1) = k1_xboole_0
% 3.79/1.00      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_4965,c_2359]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5241,plain,
% 3.79/1.00      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.79/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_4965,c_2356]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5290,plain,
% 3.79/1.00      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_5242,c_45,c_5241]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5296,plain,
% 3.79/1.00      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
% 3.79/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_4298,c_5290]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5373,plain,
% 3.79/1.00      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_5296,c_3566]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9851,plain,
% 3.79/1.00      ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) = iProver_top ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_9817,c_5373]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_8493,plain,
% 3.79/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.79/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_8457,c_5367]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9622,plain,
% 3.79/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.79/1.00      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_6169,c_8493]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_10972,plain,
% 3.79/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
% 3.79/1.00      | u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) ),
% 3.79/1.00      inference(light_normalisation,[status(thm)],[c_9622,c_9817]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5046,plain,
% 3.79/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_4960,c_47,c_2692]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9855,plain,
% 3.79/1.00      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_9817,c_5046]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_13876,plain,
% 3.79/1.00      ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
% 3.79/1.00      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_10972,c_9855]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_14598,plain,
% 3.79/1.00      ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_9864,c_9851,c_13876]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9852,plain,
% 3.79/1.00      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_9817,c_5367]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_14627,plain,
% 3.79/1.00      ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_14598,c_9852]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4872,plain,
% 3.79/1.00      ( k1_relset_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3)
% 3.79/1.00      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_4297,c_2364]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5013,plain,
% 3.79/1.00      ( k1_relset_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_2365,c_4872]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5258,plain,
% 3.79/1.00      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top
% 3.79/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.79/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_5013,c_2356]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5720,plain,
% 3.79/1.00      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_5258,c_45,c_28,c_47,c_3320,c_3321,c_3565,c_3566,
% 3.79/1.00                 c_4997,c_5008]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9846,plain,
% 3.79/1.00      ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_9817,c_5720]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(contradiction,plain,
% 3.79/1.00      ( $false ),
% 3.79/1.00      inference(minisat,[status(thm)],[c_14627,c_9846]) ).
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/1.00  
% 3.79/1.00  ------                               Statistics
% 3.79/1.00  
% 3.79/1.00  ------ General
% 3.79/1.00  
% 3.79/1.00  abstr_ref_over_cycles:                  0
% 3.79/1.00  abstr_ref_under_cycles:                 0
% 3.79/1.00  gc_basic_clause_elim:                   0
% 3.79/1.00  forced_gc_time:                         0
% 3.79/1.00  parsing_time:                           0.014
% 3.79/1.00  unif_index_cands_time:                  0.
% 3.79/1.00  unif_index_add_time:                    0.
% 3.79/1.00  orderings_time:                         0.
% 3.79/1.00  out_proof_time:                         0.027
% 3.79/1.00  total_time:                             0.448
% 3.79/1.00  num_of_symbols:                         52
% 3.79/1.00  num_of_terms:                           9320
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing
% 3.79/1.00  
% 3.79/1.00  num_of_splits:                          0
% 3.79/1.00  num_of_split_atoms:                     0
% 3.79/1.00  num_of_reused_defs:                     0
% 3.79/1.00  num_eq_ax_congr_red:                    15
% 3.79/1.00  num_of_sem_filtered_clauses:            1
% 3.79/1.00  num_of_subtypes:                        0
% 3.79/1.00  monotx_restored_types:                  0
% 3.79/1.00  sat_num_of_epr_types:                   0
% 3.79/1.00  sat_num_of_non_cyclic_types:            0
% 3.79/1.00  sat_guarded_non_collapsed_types:        0
% 3.79/1.00  num_pure_diseq_elim:                    0
% 3.79/1.00  simp_replaced_by:                       0
% 3.79/1.00  res_preprocessed:                       162
% 3.79/1.00  prep_upred:                             0
% 3.79/1.00  prep_unflattend:                        20
% 3.79/1.00  smt_new_axioms:                         0
% 3.79/1.00  pred_elim_cands:                        7
% 3.79/1.00  pred_elim:                              2
% 3.79/1.00  pred_elim_cl:                           3
% 3.79/1.00  pred_elim_cycles:                       5
% 3.79/1.00  merged_defs:                            8
% 3.79/1.00  merged_defs_ncl:                        0
% 3.79/1.00  bin_hyper_res:                          8
% 3.79/1.00  prep_cycles:                            4
% 3.79/1.00  pred_elim_time:                         0.02
% 3.79/1.00  splitting_time:                         0.
% 3.79/1.00  sem_filter_time:                        0.
% 3.79/1.00  monotx_time:                            0.001
% 3.79/1.00  subtype_inf_time:                       0.
% 3.79/1.00  
% 3.79/1.00  ------ Problem properties
% 3.79/1.00  
% 3.79/1.00  clauses:                                32
% 3.79/1.00  conjectures:                            13
% 3.79/1.00  epr:                                    9
% 3.79/1.00  horn:                                   27
% 3.79/1.00  ground:                                 13
% 3.79/1.00  unary:                                  12
% 3.79/1.00  binary:                                 6
% 3.79/1.00  lits:                                   102
% 3.79/1.00  lits_eq:                                13
% 3.79/1.00  fd_pure:                                0
% 3.79/1.00  fd_pseudo:                              0
% 3.79/1.00  fd_cond:                                3
% 3.79/1.00  fd_pseudo_cond:                         1
% 3.79/1.00  ac_symbols:                             0
% 3.79/1.00  
% 3.79/1.00  ------ Propositional Solver
% 3.79/1.00  
% 3.79/1.00  prop_solver_calls:                      27
% 3.79/1.00  prop_fast_solver_calls:                 2128
% 3.79/1.00  smt_solver_calls:                       0
% 3.79/1.00  smt_fast_solver_calls:                  0
% 3.79/1.00  prop_num_of_clauses:                    4112
% 3.79/1.00  prop_preprocess_simplified:             9190
% 3.79/1.00  prop_fo_subsumed:                       180
% 3.79/1.00  prop_solver_time:                       0.
% 3.79/1.00  smt_solver_time:                        0.
% 3.79/1.00  smt_fast_solver_time:                   0.
% 3.79/1.00  prop_fast_solver_time:                  0.
% 3.79/1.00  prop_unsat_core_time:                   0.
% 3.79/1.00  
% 3.79/1.00  ------ QBF
% 3.79/1.00  
% 3.79/1.00  qbf_q_res:                              0
% 3.79/1.00  qbf_num_tautologies:                    0
% 3.79/1.00  qbf_prep_cycles:                        0
% 3.79/1.00  
% 3.79/1.00  ------ BMC1
% 3.79/1.00  
% 3.79/1.00  bmc1_current_bound:                     -1
% 3.79/1.00  bmc1_last_solved_bound:                 -1
% 3.79/1.00  bmc1_unsat_core_size:                   -1
% 3.79/1.00  bmc1_unsat_core_parents_size:           -1
% 3.79/1.00  bmc1_merge_next_fun:                    0
% 3.79/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.79/1.00  
% 3.79/1.00  ------ Instantiation
% 3.79/1.00  
% 3.79/1.00  inst_num_of_clauses:                    1275
% 3.79/1.00  inst_num_in_passive:                    139
% 3.79/1.00  inst_num_in_active:                     700
% 3.79/1.00  inst_num_in_unprocessed:                436
% 3.79/1.00  inst_num_of_loops:                      820
% 3.79/1.00  inst_num_of_learning_restarts:          0
% 3.79/1.00  inst_num_moves_active_passive:          118
% 3.79/1.00  inst_lit_activity:                      0
% 3.79/1.00  inst_lit_activity_moves:                0
% 3.79/1.00  inst_num_tautologies:                   0
% 3.79/1.00  inst_num_prop_implied:                  0
% 3.79/1.00  inst_num_existing_simplified:           0
% 3.79/1.00  inst_num_eq_res_simplified:             0
% 3.79/1.00  inst_num_child_elim:                    0
% 3.79/1.00  inst_num_of_dismatching_blockings:      241
% 3.79/1.00  inst_num_of_non_proper_insts:           1179
% 3.79/1.00  inst_num_of_duplicates:                 0
% 3.79/1.00  inst_inst_num_from_inst_to_res:         0
% 3.79/1.00  inst_dismatching_checking_time:         0.
% 3.79/1.00  
% 3.79/1.00  ------ Resolution
% 3.79/1.00  
% 3.79/1.00  res_num_of_clauses:                     0
% 3.79/1.00  res_num_in_passive:                     0
% 3.79/1.00  res_num_in_active:                      0
% 3.79/1.00  res_num_of_loops:                       166
% 3.79/1.00  res_forward_subset_subsumed:            65
% 3.79/1.00  res_backward_subset_subsumed:           0
% 3.79/1.00  res_forward_subsumed:                   0
% 3.79/1.00  res_backward_subsumed:                  0
% 3.79/1.00  res_forward_subsumption_resolution:     0
% 3.79/1.00  res_backward_subsumption_resolution:    0
% 3.79/1.00  res_clause_to_clause_subsumption:       830
% 3.79/1.00  res_orphan_elimination:                 0
% 3.79/1.00  res_tautology_del:                      70
% 3.79/1.00  res_num_eq_res_simplified:              0
% 3.79/1.00  res_num_sel_changes:                    0
% 3.79/1.00  res_moves_from_active_to_pass:          0
% 3.79/1.00  
% 3.79/1.00  ------ Superposition
% 3.79/1.00  
% 3.79/1.00  sup_time_total:                         0.
% 3.79/1.00  sup_time_generating:                    0.
% 3.79/1.00  sup_time_sim_full:                      0.
% 3.79/1.00  sup_time_sim_immed:                     0.
% 3.79/1.00  
% 3.79/1.00  sup_num_of_clauses:                     166
% 3.79/1.00  sup_num_in_active:                      36
% 3.79/1.00  sup_num_in_passive:                     130
% 3.79/1.00  sup_num_of_loops:                       162
% 3.79/1.00  sup_fw_superposition:                   124
% 3.79/1.00  sup_bw_superposition:                   380
% 3.79/1.00  sup_immediate_simplified:               150
% 3.79/1.00  sup_given_eliminated:                   0
% 3.79/1.00  comparisons_done:                       0
% 3.79/1.00  comparisons_avoided:                    37
% 3.79/1.00  
% 3.79/1.00  ------ Simplifications
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  sim_fw_subset_subsumed:                 119
% 3.79/1.00  sim_bw_subset_subsumed:                 96
% 3.79/1.00  sim_fw_subsumed:                        25
% 3.79/1.00  sim_bw_subsumed:                        2
% 3.79/1.00  sim_fw_subsumption_res:                 2
% 3.79/1.00  sim_bw_subsumption_res:                 0
% 3.79/1.00  sim_tautology_del:                      15
% 3.79/1.00  sim_eq_tautology_del:                   18
% 3.79/1.00  sim_eq_res_simp:                        1
% 3.79/1.00  sim_fw_demodulated:                     0
% 3.79/1.00  sim_bw_demodulated:                     94
% 3.79/1.00  sim_light_normalised:                   26
% 3.79/1.00  sim_joinable_taut:                      0
% 3.79/1.00  sim_joinable_simp:                      0
% 3.79/1.00  sim_ac_normalised:                      0
% 3.79/1.00  sim_smt_subsumption:                    0
% 3.79/1.00  
%------------------------------------------------------------------------------
