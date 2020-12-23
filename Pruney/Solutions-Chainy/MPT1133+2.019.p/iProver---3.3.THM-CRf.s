%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:51 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  241 (5209 expanded)
%              Number of clauses        :  158 (1164 expanded)
%              Number of leaves         :   21 (1584 expanded)
%              Depth                    :   27
%              Number of atoms          : 1091 (60957 expanded)
%              Number of equality atoms :  456 (6465 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

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
    inference(flattening,[],[f46])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f47])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f58,plain,(
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

fof(f57,plain,(
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

fof(f56,plain,(
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

fof(f55,plain,
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

fof(f59,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f54,f58,f57,f56,f55])).

fof(f89,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f30])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f93,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f28])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f42])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f100,plain,(
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
    inference(equality_resolution,[],[f81])).

fof(f84,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f85,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f86,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f87,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f40,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f79,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f77,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

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
    inference(flattening,[],[f44])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f103,plain,(
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
    inference(equality_resolution,[],[f82])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f101,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f96,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f102,plain,(
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
    inference(equality_resolution,[],[f83])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2651,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_26,negated_conjecture,
    ( sK2 = sK3 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2697,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2651,c_26])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2652,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2700,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2652,c_26])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2669,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5458,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2700,c_2669])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2665,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_partfun1(X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6980,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(sK3,u1_struct_0(sK0),X0) != iProver_top
    | v1_partfun1(sK3,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5458,c_2665])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_44,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2655,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2671,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3793,plain,
    ( k2_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2655,c_2671])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2673,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4476,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3793,c_2673])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5211,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4476,c_46])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2675,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5216,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5211,c_2675])).

cnf(c_13,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2667,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5810,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),X0) = iProver_top
    | v1_partfun1(sK3,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5458,c_2667])).

cnf(c_10841,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_partfun1(sK3,u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5810,c_44])).

cnf(c_10842,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),X0) = iProver_top
    | v1_partfun1(sK3,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10841])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2670,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5510,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2655,c_2670])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f100])).

cnf(c_2661,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6536,plain,
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
    inference(superposition,[status(thm)],[c_2655,c_2661])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_37,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_38,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_39,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_40,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_45,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,negated_conjecture,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2656,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2751,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2656,c_26])).

cnf(c_19,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3751,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3752,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3751])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2988,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3934,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_2988])).

cnf(c_3935,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3934])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2672,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3815,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2700,c_2672])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2674,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4576,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3815,c_2674])).

cnf(c_5041,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4576,c_2700])).

cnf(c_5046,plain,
    ( r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5041,c_2675])).

cnf(c_18,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_5244,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_5245,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5244])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f103])).

cnf(c_2658,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6249,plain,
    ( v5_pre_topc(sK3,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,X0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5510,c_2658])).

cnf(c_6364,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6249])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f101])).

cnf(c_2660,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5293,plain,
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
    inference(superposition,[status(thm)],[c_2655,c_2660])).

cnf(c_24,negated_conjecture,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2657,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2756,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2657,c_26])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f102])).

cnf(c_2659,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6248,plain,
    ( v5_pre_topc(sK3,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,X0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5510,c_2659])).

cnf(c_6361,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6248])).

cnf(c_6403,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5293,c_37,c_38,c_39,c_40,c_44,c_45,c_2756,c_2697,c_2700,c_3752,c_3935,c_5046,c_5245,c_6361])).

cnf(c_6404,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6403])).

cnf(c_7498,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6536,c_37,c_38,c_39,c_40,c_44,c_45,c_2751,c_2697,c_2700,c_3752,c_3935,c_5046,c_5245,c_6364,c_6404])).

cnf(c_7499,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7498])).

cnf(c_7506,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5510,c_7499])).

cnf(c_8955,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7506,c_5046])).

cnf(c_10850,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10842,c_8955])).

cnf(c_16977,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | k1_xboole_0 = X0
    | v1_funct_2(sK3,u1_struct_0(sK0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6980,c_44,c_5216,c_10850])).

cnf(c_16978,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(sK3,u1_struct_0(sK0),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16977])).

cnf(c_16986,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2697,c_16978])).

cnf(c_6977,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_partfun1(sK3,u1_struct_0(sK0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2700,c_2665])).

cnf(c_7620,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK0)) = iProver_top
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6977,c_44,c_2697])).

cnf(c_7621,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | v1_partfun1(sK3,u1_struct_0(sK0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7620])).

cnf(c_17211,plain,
    ( u1_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16986,c_44,c_2697,c_5216,c_6977,c_10850])).

cnf(c_5457,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2655,c_2669])).

cnf(c_6101,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5457,c_2675])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2676,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3548,plain,
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
    inference(superposition,[status(thm)],[c_2655,c_2658])).

cnf(c_61,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_63,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_64,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_66,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_2989,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2988])).

cnf(c_2991,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2989])).

cnf(c_4054,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3548,c_37,c_38,c_39,c_40,c_44,c_45,c_63,c_66,c_2991])).

cnf(c_4055,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4054])).

cnf(c_4062,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2676,c_4055])).

cnf(c_4069,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4062,c_2756])).

cnf(c_8392,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6101,c_4069])).

cnf(c_3814,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2655,c_2672])).

cnf(c_4575,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3814,c_2674])).

cnf(c_5219,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4575,c_46])).

cnf(c_5224,plain,
    ( r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5219,c_2675])).

cnf(c_5511,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2700,c_2670])).

cnf(c_5916,plain,
    ( v5_pre_topc(sK3,X0,sK1) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5511,c_2660])).

cnf(c_5999,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5916])).

cnf(c_4305,plain,
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
    inference(superposition,[status(thm)],[c_2655,c_2659])).

cnf(c_4756,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4305,c_37,c_38,c_39,c_40,c_44,c_45,c_63,c_66,c_2991])).

cnf(c_4757,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4756])).

cnf(c_4765,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2751,c_4757])).

cnf(c_5917,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5511,c_4765])).

cnf(c_6539,plain,
    ( v5_pre_topc(sK3,X0,sK1) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5511,c_2661])).

cnf(c_6732,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6539])).

cnf(c_5909,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(X0,u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5511,c_2675])).

cnf(c_7728,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5909,c_4069])).

cnf(c_12523,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8392,c_37,c_38,c_39,c_40,c_44,c_2697,c_2700,c_5224,c_5999,c_5917,c_6732,c_7728])).

cnf(c_12524,plain,
    ( v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12523])).

cnf(c_12527,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12524,c_37,c_38,c_39,c_40,c_44,c_2697,c_2700,c_5224,c_5999,c_5917,c_6732,c_7728])).

cnf(c_17229,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17211,c_12527])).

cnf(c_6104,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0) = iProver_top
    | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5457,c_2667])).

cnf(c_3122,plain,
    ( v1_funct_2(sK3,X0,X1)
    | ~ v1_partfun1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3690,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)
    | ~ v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3122])).

cnf(c_3691,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0) = iProver_top
    | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3690])).

cnf(c_11747,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6104,c_44,c_3691,c_5457])).

cnf(c_11748,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0) = iProver_top
    | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11747])).

cnf(c_12532,plain,
    ( v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11748,c_12527])).

cnf(c_1815,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_3147,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | X2 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1815])).

cnf(c_3300,plain,
    ( v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3147])).

cnf(c_4138,plain,
    ( v1_funct_2(sK3,X0,k1_xboole_0)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | sK3 != sK3
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_3300])).

cnf(c_6085,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | sK3 != sK3
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_4138])).

cnf(c_6095,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | sK3 != sK3
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6085])).

cnf(c_3794,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2700,c_2671])).

cnf(c_4477,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3794,c_2673])).

cnf(c_5033,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4477,c_2700])).

cnf(c_5038,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5033,c_2675])).

cnf(c_1809,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4077,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_1809])).

cnf(c_3301,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1809])).

cnf(c_3141,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | v1_partfun1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3279,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_3141])).

cnf(c_3280,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3279])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17229,c_12532,c_6095,c_5038,c_4077,c_3301,c_3280,c_46,c_45,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:44:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.88/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.88/0.99  
% 3.88/0.99  ------  iProver source info
% 3.88/0.99  
% 3.88/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.88/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.88/0.99  git: non_committed_changes: false
% 3.88/0.99  git: last_make_outside_of_git: false
% 3.88/0.99  
% 3.88/0.99  ------ 
% 3.88/0.99  
% 3.88/0.99  ------ Input Options
% 3.88/0.99  
% 3.88/0.99  --out_options                           all
% 3.88/0.99  --tptp_safe_out                         true
% 3.88/0.99  --problem_path                          ""
% 3.88/0.99  --include_path                          ""
% 3.88/0.99  --clausifier                            res/vclausify_rel
% 3.88/0.99  --clausifier_options                    --mode clausify
% 3.88/0.99  --stdin                                 false
% 3.88/0.99  --stats_out                             all
% 3.88/0.99  
% 3.88/0.99  ------ General Options
% 3.88/0.99  
% 3.88/0.99  --fof                                   false
% 3.88/0.99  --time_out_real                         305.
% 3.88/0.99  --time_out_virtual                      -1.
% 3.88/0.99  --symbol_type_check                     false
% 3.88/0.99  --clausify_out                          false
% 3.88/0.99  --sig_cnt_out                           false
% 3.88/0.99  --trig_cnt_out                          false
% 3.88/0.99  --trig_cnt_out_tolerance                1.
% 3.88/0.99  --trig_cnt_out_sk_spl                   false
% 3.88/0.99  --abstr_cl_out                          false
% 3.88/0.99  
% 3.88/0.99  ------ Global Options
% 3.88/0.99  
% 3.88/0.99  --schedule                              default
% 3.88/0.99  --add_important_lit                     false
% 3.88/0.99  --prop_solver_per_cl                    1000
% 3.88/0.99  --min_unsat_core                        false
% 3.88/0.99  --soft_assumptions                      false
% 3.88/0.99  --soft_lemma_size                       3
% 3.88/0.99  --prop_impl_unit_size                   0
% 3.88/0.99  --prop_impl_unit                        []
% 3.88/0.99  --share_sel_clauses                     true
% 3.88/0.99  --reset_solvers                         false
% 3.88/0.99  --bc_imp_inh                            [conj_cone]
% 3.88/0.99  --conj_cone_tolerance                   3.
% 3.88/0.99  --extra_neg_conj                        none
% 3.88/0.99  --large_theory_mode                     true
% 3.88/0.99  --prolific_symb_bound                   200
% 3.88/0.99  --lt_threshold                          2000
% 3.88/0.99  --clause_weak_htbl                      true
% 3.88/0.99  --gc_record_bc_elim                     false
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing Options
% 3.88/0.99  
% 3.88/0.99  --preprocessing_flag                    true
% 3.88/0.99  --time_out_prep_mult                    0.1
% 3.88/0.99  --splitting_mode                        input
% 3.88/0.99  --splitting_grd                         true
% 3.88/0.99  --splitting_cvd                         false
% 3.88/0.99  --splitting_cvd_svl                     false
% 3.88/0.99  --splitting_nvd                         32
% 3.88/0.99  --sub_typing                            true
% 3.88/0.99  --prep_gs_sim                           true
% 3.88/0.99  --prep_unflatten                        true
% 3.88/0.99  --prep_res_sim                          true
% 3.88/0.99  --prep_upred                            true
% 3.88/0.99  --prep_sem_filter                       exhaustive
% 3.88/0.99  --prep_sem_filter_out                   false
% 3.88/0.99  --pred_elim                             true
% 3.88/0.99  --res_sim_input                         true
% 3.88/0.99  --eq_ax_congr_red                       true
% 3.88/0.99  --pure_diseq_elim                       true
% 3.88/0.99  --brand_transform                       false
% 3.88/0.99  --non_eq_to_eq                          false
% 3.88/0.99  --prep_def_merge                        true
% 3.88/0.99  --prep_def_merge_prop_impl              false
% 3.88/0.99  --prep_def_merge_mbd                    true
% 3.88/0.99  --prep_def_merge_tr_red                 false
% 3.88/0.99  --prep_def_merge_tr_cl                  false
% 3.88/0.99  --smt_preprocessing                     true
% 3.88/0.99  --smt_ac_axioms                         fast
% 3.88/0.99  --preprocessed_out                      false
% 3.88/0.99  --preprocessed_stats                    false
% 3.88/0.99  
% 3.88/0.99  ------ Abstraction refinement Options
% 3.88/0.99  
% 3.88/0.99  --abstr_ref                             []
% 3.88/0.99  --abstr_ref_prep                        false
% 3.88/0.99  --abstr_ref_until_sat                   false
% 3.88/0.99  --abstr_ref_sig_restrict                funpre
% 3.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.88/0.99  --abstr_ref_under                       []
% 3.88/0.99  
% 3.88/0.99  ------ SAT Options
% 3.88/0.99  
% 3.88/0.99  --sat_mode                              false
% 3.88/0.99  --sat_fm_restart_options                ""
% 3.88/0.99  --sat_gr_def                            false
% 3.88/0.99  --sat_epr_types                         true
% 3.88/0.99  --sat_non_cyclic_types                  false
% 3.88/0.99  --sat_finite_models                     false
% 3.88/0.99  --sat_fm_lemmas                         false
% 3.88/0.99  --sat_fm_prep                           false
% 3.88/0.99  --sat_fm_uc_incr                        true
% 3.88/0.99  --sat_out_model                         small
% 3.88/0.99  --sat_out_clauses                       false
% 3.88/0.99  
% 3.88/0.99  ------ QBF Options
% 3.88/0.99  
% 3.88/0.99  --qbf_mode                              false
% 3.88/0.99  --qbf_elim_univ                         false
% 3.88/0.99  --qbf_dom_inst                          none
% 3.88/0.99  --qbf_dom_pre_inst                      false
% 3.88/0.99  --qbf_sk_in                             false
% 3.88/0.99  --qbf_pred_elim                         true
% 3.88/0.99  --qbf_split                             512
% 3.88/0.99  
% 3.88/0.99  ------ BMC1 Options
% 3.88/0.99  
% 3.88/0.99  --bmc1_incremental                      false
% 3.88/0.99  --bmc1_axioms                           reachable_all
% 3.88/0.99  --bmc1_min_bound                        0
% 3.88/0.99  --bmc1_max_bound                        -1
% 3.88/0.99  --bmc1_max_bound_default                -1
% 3.88/0.99  --bmc1_symbol_reachability              true
% 3.88/0.99  --bmc1_property_lemmas                  false
% 3.88/0.99  --bmc1_k_induction                      false
% 3.88/0.99  --bmc1_non_equiv_states                 false
% 3.88/0.99  --bmc1_deadlock                         false
% 3.88/0.99  --bmc1_ucm                              false
% 3.88/0.99  --bmc1_add_unsat_core                   none
% 3.88/0.99  --bmc1_unsat_core_children              false
% 3.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.88/0.99  --bmc1_out_stat                         full
% 3.88/0.99  --bmc1_ground_init                      false
% 3.88/0.99  --bmc1_pre_inst_next_state              false
% 3.88/0.99  --bmc1_pre_inst_state                   false
% 3.88/0.99  --bmc1_pre_inst_reach_state             false
% 3.88/0.99  --bmc1_out_unsat_core                   false
% 3.88/0.99  --bmc1_aig_witness_out                  false
% 3.88/0.99  --bmc1_verbose                          false
% 3.88/0.99  --bmc1_dump_clauses_tptp                false
% 3.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.88/0.99  --bmc1_dump_file                        -
% 3.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.88/0.99  --bmc1_ucm_extend_mode                  1
% 3.88/0.99  --bmc1_ucm_init_mode                    2
% 3.88/0.99  --bmc1_ucm_cone_mode                    none
% 3.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.88/0.99  --bmc1_ucm_relax_model                  4
% 3.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.88/0.99  --bmc1_ucm_layered_model                none
% 3.88/0.99  --bmc1_ucm_max_lemma_size               10
% 3.88/0.99  
% 3.88/0.99  ------ AIG Options
% 3.88/0.99  
% 3.88/0.99  --aig_mode                              false
% 3.88/0.99  
% 3.88/0.99  ------ Instantiation Options
% 3.88/0.99  
% 3.88/0.99  --instantiation_flag                    true
% 3.88/0.99  --inst_sos_flag                         false
% 3.88/0.99  --inst_sos_phase                        true
% 3.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.88/0.99  --inst_lit_sel_side                     num_symb
% 3.88/0.99  --inst_solver_per_active                1400
% 3.88/0.99  --inst_solver_calls_frac                1.
% 3.88/0.99  --inst_passive_queue_type               priority_queues
% 3.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.88/0.99  --inst_passive_queues_freq              [25;2]
% 3.88/0.99  --inst_dismatching                      true
% 3.88/0.99  --inst_eager_unprocessed_to_passive     true
% 3.88/0.99  --inst_prop_sim_given                   true
% 3.88/0.99  --inst_prop_sim_new                     false
% 3.88/0.99  --inst_subs_new                         false
% 3.88/0.99  --inst_eq_res_simp                      false
% 3.88/0.99  --inst_subs_given                       false
% 3.88/0.99  --inst_orphan_elimination               true
% 3.88/0.99  --inst_learning_loop_flag               true
% 3.88/0.99  --inst_learning_start                   3000
% 3.88/0.99  --inst_learning_factor                  2
% 3.88/0.99  --inst_start_prop_sim_after_learn       3
% 3.88/0.99  --inst_sel_renew                        solver
% 3.88/0.99  --inst_lit_activity_flag                true
% 3.88/0.99  --inst_restr_to_given                   false
% 3.88/0.99  --inst_activity_threshold               500
% 3.88/0.99  --inst_out_proof                        true
% 3.88/0.99  
% 3.88/0.99  ------ Resolution Options
% 3.88/0.99  
% 3.88/0.99  --resolution_flag                       true
% 3.88/0.99  --res_lit_sel                           adaptive
% 3.88/0.99  --res_lit_sel_side                      none
% 3.88/0.99  --res_ordering                          kbo
% 3.88/0.99  --res_to_prop_solver                    active
% 3.88/0.99  --res_prop_simpl_new                    false
% 3.88/0.99  --res_prop_simpl_given                  true
% 3.88/0.99  --res_passive_queue_type                priority_queues
% 3.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.88/0.99  --res_passive_queues_freq               [15;5]
% 3.88/0.99  --res_forward_subs                      full
% 3.88/0.99  --res_backward_subs                     full
% 3.88/0.99  --res_forward_subs_resolution           true
% 3.88/0.99  --res_backward_subs_resolution          true
% 3.88/0.99  --res_orphan_elimination                true
% 3.88/0.99  --res_time_limit                        2.
% 3.88/0.99  --res_out_proof                         true
% 3.88/0.99  
% 3.88/0.99  ------ Superposition Options
% 3.88/0.99  
% 3.88/0.99  --superposition_flag                    true
% 3.88/0.99  --sup_passive_queue_type                priority_queues
% 3.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.88/0.99  --demod_completeness_check              fast
% 3.88/0.99  --demod_use_ground                      true
% 3.88/0.99  --sup_to_prop_solver                    passive
% 3.88/0.99  --sup_prop_simpl_new                    true
% 3.88/0.99  --sup_prop_simpl_given                  true
% 3.88/0.99  --sup_fun_splitting                     false
% 3.88/0.99  --sup_smt_interval                      50000
% 3.88/0.99  
% 3.88/0.99  ------ Superposition Simplification Setup
% 3.88/0.99  
% 3.88/0.99  --sup_indices_passive                   []
% 3.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/0.99  --sup_full_bw                           [BwDemod]
% 3.88/0.99  --sup_immed_triv                        [TrivRules]
% 3.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/0.99  --sup_immed_bw_main                     []
% 3.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.88/0.99  
% 3.88/0.99  ------ Combination Options
% 3.88/0.99  
% 3.88/0.99  --comb_res_mult                         3
% 3.88/0.99  --comb_sup_mult                         2
% 3.88/0.99  --comb_inst_mult                        10
% 3.88/0.99  
% 3.88/0.99  ------ Debug Options
% 3.88/0.99  
% 3.88/0.99  --dbg_backtrace                         false
% 3.88/0.99  --dbg_dump_prop_clauses                 false
% 3.88/0.99  --dbg_dump_prop_clauses_file            -
% 3.88/0.99  --dbg_out_stat                          false
% 3.88/0.99  ------ Parsing...
% 3.88/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  ------ Proving...
% 3.88/0.99  ------ Problem Properties 
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  clauses                                 35
% 3.88/0.99  conjectures                             13
% 3.88/0.99  EPR                                     9
% 3.88/0.99  Horn                                    33
% 3.88/0.99  unary                                   13
% 3.88/0.99  binary                                  10
% 3.88/0.99  lits                                    106
% 3.88/0.99  lits eq                                 5
% 3.88/0.99  fd_pure                                 0
% 3.88/0.99  fd_pseudo                               0
% 3.88/0.99  fd_cond                                 1
% 3.88/0.99  fd_pseudo_cond                          1
% 3.88/0.99  AC symbols                              0
% 3.88/0.99  
% 3.88/0.99  ------ Schedule dynamic 5 is on 
% 3.88/0.99  
% 3.88/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ 
% 3.88/0.99  Current options:
% 3.88/0.99  ------ 
% 3.88/0.99  
% 3.88/0.99  ------ Input Options
% 3.88/0.99  
% 3.88/0.99  --out_options                           all
% 3.88/0.99  --tptp_safe_out                         true
% 3.88/0.99  --problem_path                          ""
% 3.88/0.99  --include_path                          ""
% 3.88/0.99  --clausifier                            res/vclausify_rel
% 3.88/0.99  --clausifier_options                    --mode clausify
% 3.88/0.99  --stdin                                 false
% 3.88/0.99  --stats_out                             all
% 3.88/0.99  
% 3.88/0.99  ------ General Options
% 3.88/0.99  
% 3.88/0.99  --fof                                   false
% 3.88/0.99  --time_out_real                         305.
% 3.88/0.99  --time_out_virtual                      -1.
% 3.88/0.99  --symbol_type_check                     false
% 3.88/0.99  --clausify_out                          false
% 3.88/0.99  --sig_cnt_out                           false
% 3.88/0.99  --trig_cnt_out                          false
% 3.88/0.99  --trig_cnt_out_tolerance                1.
% 3.88/0.99  --trig_cnt_out_sk_spl                   false
% 3.88/0.99  --abstr_cl_out                          false
% 3.88/0.99  
% 3.88/0.99  ------ Global Options
% 3.88/0.99  
% 3.88/0.99  --schedule                              default
% 3.88/0.99  --add_important_lit                     false
% 3.88/0.99  --prop_solver_per_cl                    1000
% 3.88/0.99  --min_unsat_core                        false
% 3.88/0.99  --soft_assumptions                      false
% 3.88/0.99  --soft_lemma_size                       3
% 3.88/0.99  --prop_impl_unit_size                   0
% 3.88/0.99  --prop_impl_unit                        []
% 3.88/0.99  --share_sel_clauses                     true
% 3.88/0.99  --reset_solvers                         false
% 3.88/0.99  --bc_imp_inh                            [conj_cone]
% 3.88/0.99  --conj_cone_tolerance                   3.
% 3.88/0.99  --extra_neg_conj                        none
% 3.88/0.99  --large_theory_mode                     true
% 3.88/0.99  --prolific_symb_bound                   200
% 3.88/0.99  --lt_threshold                          2000
% 3.88/0.99  --clause_weak_htbl                      true
% 3.88/0.99  --gc_record_bc_elim                     false
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing Options
% 3.88/0.99  
% 3.88/0.99  --preprocessing_flag                    true
% 3.88/0.99  --time_out_prep_mult                    0.1
% 3.88/0.99  --splitting_mode                        input
% 3.88/0.99  --splitting_grd                         true
% 3.88/0.99  --splitting_cvd                         false
% 3.88/0.99  --splitting_cvd_svl                     false
% 3.88/0.99  --splitting_nvd                         32
% 3.88/0.99  --sub_typing                            true
% 3.88/0.99  --prep_gs_sim                           true
% 3.88/0.99  --prep_unflatten                        true
% 3.88/0.99  --prep_res_sim                          true
% 3.88/0.99  --prep_upred                            true
% 3.88/0.99  --prep_sem_filter                       exhaustive
% 3.88/0.99  --prep_sem_filter_out                   false
% 3.88/0.99  --pred_elim                             true
% 3.88/0.99  --res_sim_input                         true
% 3.88/0.99  --eq_ax_congr_red                       true
% 3.88/0.99  --pure_diseq_elim                       true
% 3.88/0.99  --brand_transform                       false
% 3.88/0.99  --non_eq_to_eq                          false
% 3.88/0.99  --prep_def_merge                        true
% 3.88/0.99  --prep_def_merge_prop_impl              false
% 3.88/0.99  --prep_def_merge_mbd                    true
% 3.88/0.99  --prep_def_merge_tr_red                 false
% 3.88/0.99  --prep_def_merge_tr_cl                  false
% 3.88/0.99  --smt_preprocessing                     true
% 3.88/0.99  --smt_ac_axioms                         fast
% 3.88/0.99  --preprocessed_out                      false
% 3.88/0.99  --preprocessed_stats                    false
% 3.88/0.99  
% 3.88/0.99  ------ Abstraction refinement Options
% 3.88/0.99  
% 3.88/0.99  --abstr_ref                             []
% 3.88/0.99  --abstr_ref_prep                        false
% 3.88/0.99  --abstr_ref_until_sat                   false
% 3.88/0.99  --abstr_ref_sig_restrict                funpre
% 3.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.88/0.99  --abstr_ref_under                       []
% 3.88/0.99  
% 3.88/0.99  ------ SAT Options
% 3.88/0.99  
% 3.88/0.99  --sat_mode                              false
% 3.88/0.99  --sat_fm_restart_options                ""
% 3.88/0.99  --sat_gr_def                            false
% 3.88/0.99  --sat_epr_types                         true
% 3.88/0.99  --sat_non_cyclic_types                  false
% 3.88/0.99  --sat_finite_models                     false
% 3.88/0.99  --sat_fm_lemmas                         false
% 3.88/0.99  --sat_fm_prep                           false
% 3.88/0.99  --sat_fm_uc_incr                        true
% 3.88/0.99  --sat_out_model                         small
% 3.88/0.99  --sat_out_clauses                       false
% 3.88/0.99  
% 3.88/0.99  ------ QBF Options
% 3.88/0.99  
% 3.88/0.99  --qbf_mode                              false
% 3.88/0.99  --qbf_elim_univ                         false
% 3.88/0.99  --qbf_dom_inst                          none
% 3.88/0.99  --qbf_dom_pre_inst                      false
% 3.88/0.99  --qbf_sk_in                             false
% 3.88/0.99  --qbf_pred_elim                         true
% 3.88/0.99  --qbf_split                             512
% 3.88/0.99  
% 3.88/0.99  ------ BMC1 Options
% 3.88/0.99  
% 3.88/0.99  --bmc1_incremental                      false
% 3.88/0.99  --bmc1_axioms                           reachable_all
% 3.88/0.99  --bmc1_min_bound                        0
% 3.88/0.99  --bmc1_max_bound                        -1
% 3.88/0.99  --bmc1_max_bound_default                -1
% 3.88/0.99  --bmc1_symbol_reachability              true
% 3.88/0.99  --bmc1_property_lemmas                  false
% 3.88/0.99  --bmc1_k_induction                      false
% 3.88/0.99  --bmc1_non_equiv_states                 false
% 3.88/0.99  --bmc1_deadlock                         false
% 3.88/0.99  --bmc1_ucm                              false
% 3.88/0.99  --bmc1_add_unsat_core                   none
% 3.88/0.99  --bmc1_unsat_core_children              false
% 3.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.88/0.99  --bmc1_out_stat                         full
% 3.88/0.99  --bmc1_ground_init                      false
% 3.88/0.99  --bmc1_pre_inst_next_state              false
% 3.88/0.99  --bmc1_pre_inst_state                   false
% 3.88/0.99  --bmc1_pre_inst_reach_state             false
% 3.88/0.99  --bmc1_out_unsat_core                   false
% 3.88/0.99  --bmc1_aig_witness_out                  false
% 3.88/0.99  --bmc1_verbose                          false
% 3.88/0.99  --bmc1_dump_clauses_tptp                false
% 3.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.88/0.99  --bmc1_dump_file                        -
% 3.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.88/0.99  --bmc1_ucm_extend_mode                  1
% 3.88/0.99  --bmc1_ucm_init_mode                    2
% 3.88/0.99  --bmc1_ucm_cone_mode                    none
% 3.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.88/0.99  --bmc1_ucm_relax_model                  4
% 3.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.88/0.99  --bmc1_ucm_layered_model                none
% 3.88/0.99  --bmc1_ucm_max_lemma_size               10
% 3.88/0.99  
% 3.88/0.99  ------ AIG Options
% 3.88/0.99  
% 3.88/0.99  --aig_mode                              false
% 3.88/0.99  
% 3.88/0.99  ------ Instantiation Options
% 3.88/0.99  
% 3.88/0.99  --instantiation_flag                    true
% 3.88/0.99  --inst_sos_flag                         false
% 3.88/0.99  --inst_sos_phase                        true
% 3.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.88/0.99  --inst_lit_sel_side                     none
% 3.88/0.99  --inst_solver_per_active                1400
% 3.88/0.99  --inst_solver_calls_frac                1.
% 3.88/0.99  --inst_passive_queue_type               priority_queues
% 3.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.88/0.99  --inst_passive_queues_freq              [25;2]
% 3.88/0.99  --inst_dismatching                      true
% 3.88/0.99  --inst_eager_unprocessed_to_passive     true
% 3.88/0.99  --inst_prop_sim_given                   true
% 3.88/0.99  --inst_prop_sim_new                     false
% 3.88/0.99  --inst_subs_new                         false
% 3.88/0.99  --inst_eq_res_simp                      false
% 3.88/0.99  --inst_subs_given                       false
% 3.88/0.99  --inst_orphan_elimination               true
% 3.88/0.99  --inst_learning_loop_flag               true
% 3.88/0.99  --inst_learning_start                   3000
% 3.88/0.99  --inst_learning_factor                  2
% 3.88/0.99  --inst_start_prop_sim_after_learn       3
% 3.88/0.99  --inst_sel_renew                        solver
% 3.88/0.99  --inst_lit_activity_flag                true
% 3.88/0.99  --inst_restr_to_given                   false
% 3.88/0.99  --inst_activity_threshold               500
% 3.88/0.99  --inst_out_proof                        true
% 3.88/0.99  
% 3.88/0.99  ------ Resolution Options
% 3.88/0.99  
% 3.88/0.99  --resolution_flag                       false
% 3.88/0.99  --res_lit_sel                           adaptive
% 3.88/0.99  --res_lit_sel_side                      none
% 3.88/0.99  --res_ordering                          kbo
% 3.88/0.99  --res_to_prop_solver                    active
% 3.88/0.99  --res_prop_simpl_new                    false
% 3.88/0.99  --res_prop_simpl_given                  true
% 3.88/0.99  --res_passive_queue_type                priority_queues
% 3.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.88/0.99  --res_passive_queues_freq               [15;5]
% 3.88/0.99  --res_forward_subs                      full
% 3.88/0.99  --res_backward_subs                     full
% 3.88/0.99  --res_forward_subs_resolution           true
% 3.88/0.99  --res_backward_subs_resolution          true
% 3.88/0.99  --res_orphan_elimination                true
% 3.88/0.99  --res_time_limit                        2.
% 3.88/0.99  --res_out_proof                         true
% 3.88/0.99  
% 3.88/0.99  ------ Superposition Options
% 3.88/0.99  
% 3.88/0.99  --superposition_flag                    true
% 3.88/0.99  --sup_passive_queue_type                priority_queues
% 3.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.88/0.99  --demod_completeness_check              fast
% 3.88/0.99  --demod_use_ground                      true
% 3.88/0.99  --sup_to_prop_solver                    passive
% 3.88/0.99  --sup_prop_simpl_new                    true
% 3.88/0.99  --sup_prop_simpl_given                  true
% 3.88/0.99  --sup_fun_splitting                     false
% 3.88/0.99  --sup_smt_interval                      50000
% 3.88/0.99  
% 3.88/0.99  ------ Superposition Simplification Setup
% 3.88/0.99  
% 3.88/0.99  --sup_indices_passive                   []
% 3.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/0.99  --sup_full_bw                           [BwDemod]
% 3.88/0.99  --sup_immed_triv                        [TrivRules]
% 3.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/0.99  --sup_immed_bw_main                     []
% 3.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.88/0.99  
% 3.88/0.99  ------ Combination Options
% 3.88/0.99  
% 3.88/0.99  --comb_res_mult                         3
% 3.88/0.99  --comb_sup_mult                         2
% 3.88/0.99  --comb_inst_mult                        10
% 3.88/0.99  
% 3.88/0.99  ------ Debug Options
% 3.88/0.99  
% 3.88/0.99  --dbg_backtrace                         false
% 3.88/0.99  --dbg_dump_prop_clauses                 false
% 3.88/0.99  --dbg_dump_prop_clauses_file            -
% 3.88/0.99  --dbg_out_stat                          false
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  % SZS status Theorem for theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  fof(f19,conjecture,(
% 3.88/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f20,negated_conjecture,(
% 3.88/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.88/0.99    inference(negated_conjecture,[],[f19])).
% 3.88/0.99  
% 3.88/0.99  fof(f46,plain,(
% 3.88/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.88/0.99    inference(ennf_transformation,[],[f20])).
% 3.88/0.99  
% 3.88/0.99  fof(f47,plain,(
% 3.88/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.88/0.99    inference(flattening,[],[f46])).
% 3.88/0.99  
% 3.88/0.99  fof(f53,plain,(
% 3.88/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.88/0.99    inference(nnf_transformation,[],[f47])).
% 3.88/0.99  
% 3.88/0.99  fof(f54,plain,(
% 3.88/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.88/0.99    inference(flattening,[],[f53])).
% 3.88/0.99  
% 3.88/0.99  fof(f58,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK3 = X2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK3))) )),
% 3.88/0.99    introduced(choice_axiom,[])).
% 3.88/0.99  
% 3.88/0.99  fof(f57,plain,(
% 3.88/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.88/0.99    introduced(choice_axiom,[])).
% 3.88/0.99  
% 3.88/0.99  fof(f56,plain,(
% 3.88/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,X0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,X0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 3.88/0.99    introduced(choice_axiom,[])).
% 3.88/0.99  
% 3.88/0.99  fof(f55,plain,(
% 3.88/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.88/0.99    introduced(choice_axiom,[])).
% 3.88/0.99  
% 3.88/0.99  fof(f59,plain,(
% 3.88/0.99    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f54,f58,f57,f56,f55])).
% 3.88/0.99  
% 3.88/0.99  fof(f89,plain,(
% 3.88/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.88/0.99    inference(cnf_transformation,[],[f59])).
% 3.88/0.99  
% 3.88/0.99  fof(f94,plain,(
% 3.88/0.99    sK2 = sK3),
% 3.88/0.99    inference(cnf_transformation,[],[f59])).
% 3.88/0.99  
% 3.88/0.99  fof(f90,plain,(
% 3.88/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.88/0.99    inference(cnf_transformation,[],[f59])).
% 3.88/0.99  
% 3.88/0.99  fof(f10,axiom,(
% 3.88/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f30,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.88/0.99    inference(ennf_transformation,[],[f10])).
% 3.88/0.99  
% 3.88/0.99  fof(f31,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.88/0.99    inference(flattening,[],[f30])).
% 3.88/0.99  
% 3.88/0.99  fof(f71,plain,(
% 3.88/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f31])).
% 3.88/0.99  
% 3.88/0.99  fof(f13,axiom,(
% 3.88/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f36,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.88/0.99    inference(ennf_transformation,[],[f13])).
% 3.88/0.99  
% 3.88/0.99  fof(f37,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.88/0.99    inference(flattening,[],[f36])).
% 3.88/0.99  
% 3.88/0.99  fof(f75,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f37])).
% 3.88/0.99  
% 3.88/0.99  fof(f91,plain,(
% 3.88/0.99    v1_funct_1(sK3)),
% 3.88/0.99    inference(cnf_transformation,[],[f59])).
% 3.88/0.99  
% 3.88/0.99  fof(f93,plain,(
% 3.88/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.88/0.99    inference(cnf_transformation,[],[f59])).
% 3.88/0.99  
% 3.88/0.99  fof(f8,axiom,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f27,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(ennf_transformation,[],[f8])).
% 3.88/0.99  
% 3.88/0.99  fof(f69,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f27])).
% 3.88/0.99  
% 3.88/0.99  fof(f6,axiom,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f25,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(ennf_transformation,[],[f6])).
% 3.88/0.99  
% 3.88/0.99  fof(f67,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f25])).
% 3.88/0.99  
% 3.88/0.99  fof(f3,axiom,(
% 3.88/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f50,plain,(
% 3.88/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.88/0.99    inference(nnf_transformation,[],[f3])).
% 3.88/0.99  
% 3.88/0.99  fof(f64,plain,(
% 3.88/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f50])).
% 3.88/0.99  
% 3.88/0.99  fof(f12,axiom,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f34,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(ennf_transformation,[],[f12])).
% 3.88/0.99  
% 3.88/0.99  fof(f35,plain,(
% 3.88/0.99    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(flattening,[],[f34])).
% 3.88/0.99  
% 3.88/0.99  fof(f74,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f35])).
% 3.88/0.99  
% 3.88/0.99  fof(f9,axiom,(
% 3.88/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f28,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.88/0.99    inference(ennf_transformation,[],[f9])).
% 3.88/0.99  
% 3.88/0.99  fof(f29,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.88/0.99    inference(flattening,[],[f28])).
% 3.88/0.99  
% 3.88/0.99  fof(f70,plain,(
% 3.88/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f29])).
% 3.88/0.99  
% 3.88/0.99  fof(f17,axiom,(
% 3.88/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f42,plain,(
% 3.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.88/0.99    inference(ennf_transformation,[],[f17])).
% 3.88/0.99  
% 3.88/0.99  fof(f43,plain,(
% 3.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.88/0.99    inference(flattening,[],[f42])).
% 3.88/0.99  
% 3.88/0.99  fof(f51,plain,(
% 3.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.88/0.99    inference(nnf_transformation,[],[f43])).
% 3.88/0.99  
% 3.88/0.99  fof(f81,plain,(
% 3.88/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f51])).
% 3.88/0.99  
% 3.88/0.99  fof(f100,plain,(
% 3.88/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.88/0.99    inference(equality_resolution,[],[f81])).
% 3.88/0.99  
% 3.88/0.99  fof(f84,plain,(
% 3.88/0.99    v2_pre_topc(sK0)),
% 3.88/0.99    inference(cnf_transformation,[],[f59])).
% 3.88/0.99  
% 3.88/0.99  fof(f85,plain,(
% 3.88/0.99    l1_pre_topc(sK0)),
% 3.88/0.99    inference(cnf_transformation,[],[f59])).
% 3.88/0.99  
% 3.88/0.99  fof(f86,plain,(
% 3.88/0.99    v2_pre_topc(sK1)),
% 3.88/0.99    inference(cnf_transformation,[],[f59])).
% 3.88/0.99  
% 3.88/0.99  fof(f87,plain,(
% 3.88/0.99    l1_pre_topc(sK1)),
% 3.88/0.99    inference(cnf_transformation,[],[f59])).
% 3.88/0.99  
% 3.88/0.99  fof(f92,plain,(
% 3.88/0.99    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.88/0.99    inference(cnf_transformation,[],[f59])).
% 3.88/0.99  
% 3.88/0.99  fof(f95,plain,(
% 3.88/0.99    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 3.88/0.99    inference(cnf_transformation,[],[f59])).
% 3.88/0.99  
% 3.88/0.99  fof(f16,axiom,(
% 3.88/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f22,plain,(
% 3.88/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 3.88/0.99    inference(pure_predicate_removal,[],[f16])).
% 3.88/0.99  
% 3.88/0.99  fof(f40,plain,(
% 3.88/0.99    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.88/0.99    inference(ennf_transformation,[],[f22])).
% 3.88/0.99  
% 3.88/0.99  fof(f41,plain,(
% 3.88/0.99    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.88/0.99    inference(flattening,[],[f40])).
% 3.88/0.99  
% 3.88/0.99  fof(f79,plain,(
% 3.88/0.99    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f41])).
% 3.88/0.99  
% 3.88/0.99  fof(f14,axiom,(
% 3.88/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f21,plain,(
% 3.88/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 3.88/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.88/0.99  
% 3.88/0.99  fof(f38,plain,(
% 3.88/0.99    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.88/0.99    inference(ennf_transformation,[],[f21])).
% 3.88/0.99  
% 3.88/0.99  fof(f77,plain,(
% 3.88/0.99    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f38])).
% 3.88/0.99  
% 3.88/0.99  fof(f7,axiom,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f26,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(ennf_transformation,[],[f7])).
% 3.88/0.99  
% 3.88/0.99  fof(f68,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f26])).
% 3.88/0.99  
% 3.88/0.99  fof(f5,axiom,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f24,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(ennf_transformation,[],[f5])).
% 3.88/0.99  
% 3.88/0.99  fof(f66,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f24])).
% 3.88/0.99  
% 3.88/0.99  fof(f15,axiom,(
% 3.88/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f39,plain,(
% 3.88/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.88/0.99    inference(ennf_transformation,[],[f15])).
% 3.88/0.99  
% 3.88/0.99  fof(f78,plain,(
% 3.88/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f39])).
% 3.88/0.99  
% 3.88/0.99  fof(f18,axiom,(
% 3.88/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f44,plain,(
% 3.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.88/0.99    inference(ennf_transformation,[],[f18])).
% 3.88/0.99  
% 3.88/0.99  fof(f45,plain,(
% 3.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.88/0.99    inference(flattening,[],[f44])).
% 3.88/0.99  
% 3.88/0.99  fof(f52,plain,(
% 3.88/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.88/0.99    inference(nnf_transformation,[],[f45])).
% 3.88/0.99  
% 3.88/0.99  fof(f82,plain,(
% 3.88/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f52])).
% 3.88/0.99  
% 3.88/0.99  fof(f103,plain,(
% 3.88/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.88/0.99    inference(equality_resolution,[],[f82])).
% 3.88/0.99  
% 3.88/0.99  fof(f80,plain,(
% 3.88/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f51])).
% 3.88/0.99  
% 3.88/0.99  fof(f101,plain,(
% 3.88/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.88/0.99    inference(equality_resolution,[],[f80])).
% 3.88/0.99  
% 3.88/0.99  fof(f96,plain,(
% 3.88/0.99    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 3.88/0.99    inference(cnf_transformation,[],[f59])).
% 3.88/0.99  
% 3.88/0.99  fof(f83,plain,(
% 3.88/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f52])).
% 3.88/0.99  
% 3.88/0.99  fof(f102,plain,(
% 3.88/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.88/0.99    inference(equality_resolution,[],[f83])).
% 3.88/0.99  
% 3.88/0.99  fof(f65,plain,(
% 3.88/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f50])).
% 3.88/0.99  
% 3.88/0.99  cnf(c_31,negated_conjecture,
% 3.88/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.88/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2651,plain,
% 3.88/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_26,negated_conjecture,
% 3.88/0.99      ( sK2 = sK3 ),
% 3.88/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2697,plain,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.88/0.99      inference(light_normalisation,[status(thm)],[c_2651,c_26]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_30,negated_conjecture,
% 3.88/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2652,plain,
% 3.88/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2700,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.88/0.99      inference(light_normalisation,[status(thm)],[c_2652,c_26]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_11,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.88/0.99      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 3.88/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2669,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5458,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) = iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2700,c_2669]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_16,plain,
% 3.88/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.88/0.99      | v1_partfun1(X0,X1)
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | ~ v1_funct_1(X0)
% 3.88/0.99      | k1_xboole_0 = X2 ),
% 3.88/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2665,plain,
% 3.88/0.99      ( k1_xboole_0 = X0
% 3.88/0.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.88/0.99      | v1_partfun1(X1,X2) = iProver_top
% 3.88/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.88/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6980,plain,
% 3.88/0.99      ( k1_xboole_0 = X0
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),X0) != iProver_top
% 3.88/0.99      | v1_partfun1(sK3,u1_struct_0(sK0)) = iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5458,c_2665]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_29,negated_conjecture,
% 3.88/0.99      ( v1_funct_1(sK3) ),
% 3.88/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_44,plain,
% 3.88/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_27,negated_conjecture,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2655,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_9,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2671,plain,
% 3.88/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.88/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3793,plain,
% 3.88/0.99      ( k2_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k2_relat_1(sK3) ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2655,c_2671]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_7,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.88/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2673,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.88/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4476,plain,
% 3.88/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_3793,c_2673]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_46,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5211,plain,
% 3.88/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_4476,c_46]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.88/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2675,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.88/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5216,plain,
% 3.88/0.99      ( r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5211,c_2675]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_13,plain,
% 3.88/0.99      ( v1_funct_2(X0,X1,X2)
% 3.88/0.99      | ~ v1_partfun1(X0,X1)
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | ~ v1_funct_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2667,plain,
% 3.88/0.99      ( v1_funct_2(X0,X1,X2) = iProver_top
% 3.88/0.99      | v1_partfun1(X0,X1) != iProver_top
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5810,plain,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(sK0),X0) = iProver_top
% 3.88/0.99      | v1_partfun1(sK3,u1_struct_0(sK0)) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5458,c_2667]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_10841,plain,
% 3.88/0.99      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.88/0.99      | v1_partfun1(sK3,u1_struct_0(sK0)) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),X0) = iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_5810,c_44]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_10842,plain,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(sK0),X0) = iProver_top
% 3.88/0.99      | v1_partfun1(sK3,u1_struct_0(sK0)) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_10841]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_10,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.88/0.99      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 3.88/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2670,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5510,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2655,c_2670]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_20,plain,
% 3.88/0.99      ( v5_pre_topc(X0,X1,X2)
% 3.88/0.99      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 3.88/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.88/0.99      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 3.88/0.99      | ~ v2_pre_topc(X1)
% 3.88/0.99      | ~ v2_pre_topc(X2)
% 3.88/0.99      | ~ l1_pre_topc(X1)
% 3.88/0.99      | ~ l1_pre_topc(X2)
% 3.88/0.99      | ~ v1_funct_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2661,plain,
% 3.88/0.99      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 3.88/0.99      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 3.88/0.99      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.88/0.99      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 3.88/0.99      | v2_pre_topc(X1) != iProver_top
% 3.88/0.99      | v2_pre_topc(X2) != iProver_top
% 3.88/0.99      | l1_pre_topc(X1) != iProver_top
% 3.88/0.99      | l1_pre_topc(X2) != iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6536,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.88/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.88/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2655,c_2661]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_36,negated_conjecture,
% 3.88/0.99      ( v2_pre_topc(sK0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_37,plain,
% 3.88/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_35,negated_conjecture,
% 3.88/0.99      ( l1_pre_topc(sK0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_38,plain,
% 3.88/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_34,negated_conjecture,
% 3.88/0.99      ( v2_pre_topc(sK1) ),
% 3.88/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_39,plain,
% 3.88/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_33,negated_conjecture,
% 3.88/0.99      ( l1_pre_topc(sK1) ),
% 3.88/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_40,plain,
% 3.88/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_28,negated_conjecture,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_45,plain,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_25,negated_conjecture,
% 3.88/0.99      ( v5_pre_topc(sK2,sK0,sK1)
% 3.88/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2656,plain,
% 3.88/0.99      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2751,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
% 3.88/0.99      inference(light_normalisation,[status(thm)],[c_2656,c_26]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19,plain,
% 3.88/0.99      ( ~ v2_pre_topc(X0)
% 3.88/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.88/0.99      | ~ l1_pre_topc(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3751,plain,
% 3.88/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.88/0.99      | ~ v2_pre_topc(sK1)
% 3.88/0.99      | ~ l1_pre_topc(sK1) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3752,plain,
% 3.88/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.88/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_3751]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_17,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.88/0.99      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.88/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2988,plain,
% 3.88/0.99      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.88/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3934,plain,
% 3.88/0.99      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.88/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_2988]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3935,plain,
% 3.88/0.99      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.88/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_3934]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_8,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2672,plain,
% 3.88/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.88/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3815,plain,
% 3.88/0.99      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2700,c_2672]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.88/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2674,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.88/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4576,plain,
% 3.88/0.99      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_3815,c_2674]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5041,plain,
% 3.88/0.99      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_4576,c_2700]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5046,plain,
% 3.88/0.99      ( r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5041,c_2675]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18,plain,
% 3.88/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.88/0.99      | ~ l1_pre_topc(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5244,plain,
% 3.88/0.99      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.88/0.99      | ~ l1_pre_topc(sK1) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5245,plain,
% 3.88/0.99      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 3.88/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_5244]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_23,plain,
% 3.88/0.99      ( ~ v5_pre_topc(X0,X1,X2)
% 3.88/0.99      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 3.88/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.88/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 3.88/0.99      | ~ v2_pre_topc(X1)
% 3.88/0.99      | ~ v2_pre_topc(X2)
% 3.88/0.99      | ~ l1_pre_topc(X1)
% 3.88/0.99      | ~ l1_pre_topc(X2)
% 3.88/0.99      | ~ v1_funct_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2658,plain,
% 3.88/0.99      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.88/0.99      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 3.88/0.99      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.88/0.99      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 3.88/0.99      | v2_pre_topc(X1) != iProver_top
% 3.88/0.99      | v2_pre_topc(X2) != iProver_top
% 3.88/0.99      | l1_pre_topc(X1) != iProver_top
% 3.88/0.99      | l1_pre_topc(X2) != iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6249,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,X0,sK1) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(X0)) != iProver_top
% 3.88/0.99      | v2_pre_topc(X0) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.88/0.99      | l1_pre_topc(X0) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5510,c_2658]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6364,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_6249]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_21,plain,
% 3.88/0.99      ( ~ v5_pre_topc(X0,X1,X2)
% 3.88/0.99      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 3.88/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.88/0.99      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 3.88/0.99      | ~ v2_pre_topc(X1)
% 3.88/0.99      | ~ v2_pre_topc(X2)
% 3.88/0.99      | ~ l1_pre_topc(X1)
% 3.88/0.99      | ~ l1_pre_topc(X2)
% 3.88/0.99      | ~ v1_funct_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2660,plain,
% 3.88/0.99      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.88/0.99      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 3.88/0.99      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.88/0.99      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 3.88/0.99      | v2_pre_topc(X1) != iProver_top
% 3.88/0.99      | v2_pre_topc(X2) != iProver_top
% 3.88/0.99      | l1_pre_topc(X1) != iProver_top
% 3.88/0.99      | l1_pre_topc(X2) != iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5293,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.88/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.88/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2655,c_2660]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_24,negated_conjecture,
% 3.88/0.99      ( ~ v5_pre_topc(sK2,sK0,sK1)
% 3.88/0.99      | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2657,plain,
% 3.88/0.99      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2756,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
% 3.88/0.99      inference(light_normalisation,[status(thm)],[c_2657,c_26]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_22,plain,
% 3.88/0.99      ( v5_pre_topc(X0,X1,X2)
% 3.88/0.99      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 3.88/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.88/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 3.88/0.99      | ~ v2_pre_topc(X1)
% 3.88/0.99      | ~ v2_pre_topc(X2)
% 3.88/0.99      | ~ l1_pre_topc(X1)
% 3.88/0.99      | ~ l1_pre_topc(X2)
% 3.88/0.99      | ~ v1_funct_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2659,plain,
% 3.88/0.99      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 3.88/0.99      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 3.88/0.99      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.88/0.99      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 3.88/0.99      | v2_pre_topc(X1) != iProver_top
% 3.88/0.99      | v2_pre_topc(X2) != iProver_top
% 3.88/0.99      | l1_pre_topc(X1) != iProver_top
% 3.88/0.99      | l1_pre_topc(X2) != iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6248,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,X0,sK1) = iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(X0)) != iProver_top
% 3.88/0.99      | v2_pre_topc(X0) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.88/0.99      | l1_pre_topc(X0) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5510,c_2659]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6361,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_6248]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6403,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_5293,c_37,c_38,c_39,c_40,c_44,c_45,c_2756,c_2697,
% 3.88/0.99                 c_2700,c_3752,c_3935,c_5046,c_5245,c_6361]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6404,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_6403]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_7498,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_6536,c_37,c_38,c_39,c_40,c_44,c_45,c_2751,c_2697,
% 3.88/0.99                 c_2700,c_3752,c_3935,c_5046,c_5245,c_6364,c_6404]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_7499,plain,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_7498]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_7506,plain,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5510,c_7499]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_8955,plain,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_7506,c_5046]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_10850,plain,
% 3.88/0.99      ( v1_partfun1(sK3,u1_struct_0(sK0)) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_10842,c_8955]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_16977,plain,
% 3.88/0.99      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.88/0.99      | k1_xboole_0 = X0
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),X0) != iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_6980,c_44,c_5216,c_10850]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_16978,plain,
% 3.88/0.99      ( k1_xboole_0 = X0
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),X0) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_16977]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_16986,plain,
% 3.88/0.99      ( u1_struct_0(sK1) = k1_xboole_0
% 3.88/0.99      | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2697,c_16978]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6977,plain,
% 3.88/0.99      ( u1_struct_0(sK1) = k1_xboole_0
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | v1_partfun1(sK3,u1_struct_0(sK0)) = iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2700,c_2665]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_7620,plain,
% 3.88/0.99      ( v1_partfun1(sK3,u1_struct_0(sK0)) = iProver_top
% 3.88/0.99      | u1_struct_0(sK1) = k1_xboole_0 ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_6977,c_44,c_2697]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_7621,plain,
% 3.88/0.99      ( u1_struct_0(sK1) = k1_xboole_0
% 3.88/0.99      | v1_partfun1(sK3,u1_struct_0(sK0)) = iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_7620]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_17211,plain,
% 3.88/0.99      ( u1_struct_0(sK1) = k1_xboole_0 ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_16986,c_44,c_2697,c_5216,c_6977,c_10850]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5457,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0))) = iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2655,c_2669]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6101,plain,
% 3.88/0.99      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.88/0.99      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)) = iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5457,c_2675]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.88/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2676,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.88/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3548,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.88/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.88/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2655,c_2658]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_61,plain,
% 3.88/0.99      ( v2_pre_topc(X0) != iProver_top
% 3.88/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 3.88/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_63,plain,
% 3.88/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.88/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_61]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_64,plain,
% 3.88/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.88/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_66,plain,
% 3.88/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 3.88/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_64]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2989,plain,
% 3.88/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 3.88/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_2988]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2991,plain,
% 3.88/0.99      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.88/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_2989]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4054,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_3548,c_37,c_38,c_39,c_40,c_44,c_45,c_63,c_66,c_2991]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4055,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_4054]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4062,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2676,c_4055]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4069,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_4062,c_2756]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_8392,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_6101,c_4069]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3814,plain,
% 3.88/0.99      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2655,c_2672]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4575,plain,
% 3.88/0.99      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_3814,c_2674]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5219,plain,
% 3.88/0.99      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_4575,c_46]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5224,plain,
% 3.88/0.99      ( r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5219,c_2675]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5511,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) = iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2700,c_2670]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5916,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,X0,sK1) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) = iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 3.88/0.99      | v2_pre_topc(X0) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.88/0.99      | l1_pre_topc(X0) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5511,c_2660]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5999,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_5916]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4305,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.88/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.88/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2655,c_2659]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4756,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_4305,c_37,c_38,c_39,c_40,c_44,c_45,c_63,c_66,c_2991]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4757,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_4756]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4765,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2751,c_4757]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5917,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5511,c_4765]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6539,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,X0,sK1) = iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 3.88/0.99      | v2_pre_topc(X0) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.88/0.99      | l1_pre_topc(X0) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5511,c_2661]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6732,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.88/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.88/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_6539]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5909,plain,
% 3.88/0.99      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.88/0.99      | r1_tarski(sK3,k2_zfmisc_1(X0,u1_struct_0(sK1))) = iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5511,c_2675]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_7728,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5909,c_4069]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_12523,plain,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.88/0.99      | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_8392,c_37,c_38,c_39,c_40,c_44,c_2697,c_2700,c_5224,
% 3.88/0.99                 c_5999,c_5917,c_6732,c_7728]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_12524,plain,
% 3.88/0.99      ( v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_12523]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_12527,plain,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_12524,c_37,c_38,c_39,c_40,c_44,c_2697,c_2700,c_5224,
% 3.88/0.99                 c_5999,c_5917,c_6732,c_7728]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_17229,plain,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_17211,c_12527]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6104,plain,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0) = iProver_top
% 3.88/0.99      | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5457,c_2667]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3122,plain,
% 3.88/0.99      ( v1_funct_2(sK3,X0,X1)
% 3.88/0.99      | ~ v1_partfun1(sK3,X0)
% 3.88/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.88/0.99      | ~ v1_funct_1(sK3) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3690,plain,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)
% 3.88/0.99      | ~ v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
% 3.88/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)))
% 3.88/0.99      | ~ v1_funct_1(sK3) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_3122]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3691,plain,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0) = iProver_top
% 3.88/0.99      | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0))) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_3690]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_11747,plain,
% 3.88/0.99      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.88/0.99      | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0) = iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_6104,c_44,c_3691,c_5457]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_11748,plain,
% 3.88/0.99      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0) = iProver_top
% 3.88/0.99      | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_11747]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_12532,plain,
% 3.88/0.99      ( v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_11748,c_12527]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1815,plain,
% 3.88/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.88/0.99      | v1_funct_2(X3,X4,X5)
% 3.88/0.99      | X3 != X0
% 3.88/0.99      | X4 != X1
% 3.88/0.99      | X5 != X2 ),
% 3.88/0.99      theory(equality) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3147,plain,
% 3.88/0.99      ( v1_funct_2(X0,X1,X2)
% 3.88/0.99      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.88/0.99      | X2 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.88/0.99      | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.88/0.99      | X0 != sK3 ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_1815]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3300,plain,
% 3.88/0.99      ( v1_funct_2(sK3,X0,X1)
% 3.88/0.99      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.88/0.99      | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.88/0.99      | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.88/0.99      | sK3 != sK3 ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_3147]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4138,plain,
% 3.88/0.99      ( v1_funct_2(sK3,X0,k1_xboole_0)
% 3.88/0.99      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.88/0.99      | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.88/0.99      | sK3 != sK3
% 3.88/0.99      | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_3300]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6085,plain,
% 3.88/0.99      ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
% 3.88/0.99      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.88/0.99      | sK3 != sK3
% 3.88/0.99      | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_4138]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6095,plain,
% 3.88/0.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.88/0.99      | sK3 != sK3
% 3.88/0.99      | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_6085]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3794,plain,
% 3.88/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k2_relat_1(sK3) ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2700,c_2671]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4477,plain,
% 3.88/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_3794,c_2673]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5033,plain,
% 3.88/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_4477,c_2700]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5038,plain,
% 3.88/0.99      ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_5033,c_2675]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1809,plain,( X0 = X0 ),theory(equality) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4077,plain,
% 3.88/0.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_1809]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3301,plain,
% 3.88/0.99      ( sK3 = sK3 ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_1809]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3141,plain,
% 3.88/0.99      ( ~ v1_funct_2(sK3,X0,X1)
% 3.88/0.99      | v1_partfun1(sK3,X0)
% 3.88/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.88/0.99      | ~ v1_funct_1(sK3)
% 3.88/0.99      | k1_xboole_0 = X1 ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3279,plain,
% 3.88/0.99      ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.88/0.99      | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
% 3.88/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.88/0.99      | ~ v1_funct_1(sK3)
% 3.88/0.99      | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_3141]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3280,plain,
% 3.88/0.99      ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.88/0.99      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.88/0.99      | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_3279]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(contradiction,plain,
% 3.88/0.99      ( $false ),
% 3.88/0.99      inference(minisat,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_17229,c_12532,c_6095,c_5038,c_4077,c_3301,c_3280,c_46,
% 3.88/0.99                 c_45,c_44]) ).
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  ------                               Statistics
% 3.88/0.99  
% 3.88/0.99  ------ General
% 3.88/0.99  
% 3.88/0.99  abstr_ref_over_cycles:                  0
% 3.88/0.99  abstr_ref_under_cycles:                 0
% 3.88/0.99  gc_basic_clause_elim:                   0
% 3.88/0.99  forced_gc_time:                         0
% 3.88/0.99  parsing_time:                           0.01
% 3.88/0.99  unif_index_cands_time:                  0.
% 3.88/0.99  unif_index_add_time:                    0.
% 3.88/0.99  orderings_time:                         0.
% 3.88/0.99  out_proof_time:                         0.019
% 3.88/0.99  total_time:                             0.475
% 3.88/0.99  num_of_symbols:                         53
% 3.88/0.99  num_of_terms:                           17558
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing
% 3.88/0.99  
% 3.88/0.99  num_of_splits:                          0
% 3.88/0.99  num_of_split_atoms:                     0
% 3.88/0.99  num_of_reused_defs:                     0
% 3.88/0.99  num_eq_ax_congr_red:                    30
% 3.88/0.99  num_of_sem_filtered_clauses:            1
% 3.88/0.99  num_of_subtypes:                        0
% 3.88/0.99  monotx_restored_types:                  0
% 3.88/0.99  sat_num_of_epr_types:                   0
% 3.88/0.99  sat_num_of_non_cyclic_types:            0
% 3.88/0.99  sat_guarded_non_collapsed_types:        0
% 3.88/0.99  num_pure_diseq_elim:                    0
% 3.88/0.99  simp_replaced_by:                       0
% 3.88/0.99  res_preprocessed:                       171
% 3.88/0.99  prep_upred:                             0
% 3.88/0.99  prep_unflattend:                        32
% 3.88/0.99  smt_new_axioms:                         0
% 3.88/0.99  pred_elim_cands:                        8
% 3.88/0.99  pred_elim:                              0
% 3.88/0.99  pred_elim_cl:                           0
% 3.88/0.99  pred_elim_cycles:                       4
% 3.88/0.99  merged_defs:                            16
% 3.88/0.99  merged_defs_ncl:                        0
% 3.88/0.99  bin_hyper_res:                          16
% 3.88/0.99  prep_cycles:                            4
% 3.88/0.99  pred_elim_time:                         0.026
% 3.88/0.99  splitting_time:                         0.
% 3.88/0.99  sem_filter_time:                        0.
% 3.88/0.99  monotx_time:                            0.001
% 3.88/0.99  subtype_inf_time:                       0.
% 3.88/0.99  
% 3.88/0.99  ------ Problem properties
% 3.88/0.99  
% 3.88/0.99  clauses:                                35
% 3.88/0.99  conjectures:                            13
% 3.88/0.99  epr:                                    9
% 3.88/0.99  horn:                                   33
% 3.88/0.99  ground:                                 13
% 3.88/0.99  unary:                                  13
% 3.88/0.99  binary:                                 10
% 3.88/0.99  lits:                                   106
% 3.88/0.99  lits_eq:                                5
% 3.88/0.99  fd_pure:                                0
% 3.88/0.99  fd_pseudo:                              0
% 3.88/0.99  fd_cond:                                1
% 3.88/0.99  fd_pseudo_cond:                         1
% 3.88/0.99  ac_symbols:                             0
% 3.88/0.99  
% 3.88/0.99  ------ Propositional Solver
% 3.88/0.99  
% 3.88/0.99  prop_solver_calls:                      29
% 3.88/0.99  prop_fast_solver_calls:                 2143
% 3.88/0.99  smt_solver_calls:                       0
% 3.88/0.99  smt_fast_solver_calls:                  0
% 3.88/0.99  prop_num_of_clauses:                    6172
% 3.88/0.99  prop_preprocess_simplified:             12313
% 3.88/0.99  prop_fo_subsumed:                       119
% 3.88/0.99  prop_solver_time:                       0.
% 3.88/0.99  smt_solver_time:                        0.
% 3.88/0.99  smt_fast_solver_time:                   0.
% 3.88/0.99  prop_fast_solver_time:                  0.
% 3.88/0.99  prop_unsat_core_time:                   0.
% 3.88/0.99  
% 3.88/0.99  ------ QBF
% 3.88/0.99  
% 3.88/0.99  qbf_q_res:                              0
% 3.88/0.99  qbf_num_tautologies:                    0
% 3.88/0.99  qbf_prep_cycles:                        0
% 3.88/0.99  
% 3.88/0.99  ------ BMC1
% 3.88/0.99  
% 3.88/0.99  bmc1_current_bound:                     -1
% 3.88/0.99  bmc1_last_solved_bound:                 -1
% 3.88/0.99  bmc1_unsat_core_size:                   -1
% 3.88/0.99  bmc1_unsat_core_parents_size:           -1
% 3.88/0.99  bmc1_merge_next_fun:                    0
% 3.88/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.88/0.99  
% 3.88/0.99  ------ Instantiation
% 3.88/0.99  
% 3.88/0.99  inst_num_of_clauses:                    1587
% 3.88/0.99  inst_num_in_passive:                    107
% 3.88/0.99  inst_num_in_active:                     744
% 3.88/0.99  inst_num_in_unprocessed:                737
% 3.88/0.99  inst_num_of_loops:                      800
% 3.88/0.99  inst_num_of_learning_restarts:          0
% 3.88/0.99  inst_num_moves_active_passive:          53
% 3.88/0.99  inst_lit_activity:                      0
% 3.88/0.99  inst_lit_activity_moves:                0
% 3.88/0.99  inst_num_tautologies:                   0
% 3.88/0.99  inst_num_prop_implied:                  0
% 3.88/0.99  inst_num_existing_simplified:           0
% 3.88/0.99  inst_num_eq_res_simplified:             0
% 3.88/0.99  inst_num_child_elim:                    0
% 3.88/0.99  inst_num_of_dismatching_blockings:      977
% 3.88/0.99  inst_num_of_non_proper_insts:           2060
% 3.88/0.99  inst_num_of_duplicates:                 0
% 3.88/0.99  inst_inst_num_from_inst_to_res:         0
% 3.88/0.99  inst_dismatching_checking_time:         0.
% 3.88/0.99  
% 3.88/0.99  ------ Resolution
% 3.88/0.99  
% 3.88/0.99  res_num_of_clauses:                     0
% 3.88/0.99  res_num_in_passive:                     0
% 3.88/0.99  res_num_in_active:                      0
% 3.88/0.99  res_num_of_loops:                       175
% 3.88/0.99  res_forward_subset_subsumed:            298
% 3.88/0.99  res_backward_subset_subsumed:           6
% 3.88/0.99  res_forward_subsumed:                   0
% 3.88/0.99  res_backward_subsumed:                  0
% 3.88/0.99  res_forward_subsumption_resolution:     0
% 3.88/0.99  res_backward_subsumption_resolution:    0
% 3.88/0.99  res_clause_to_clause_subsumption:       1165
% 3.88/0.99  res_orphan_elimination:                 0
% 3.88/0.99  res_tautology_del:                      221
% 3.88/0.99  res_num_eq_res_simplified:              0
% 3.88/0.99  res_num_sel_changes:                    0
% 3.88/0.99  res_moves_from_active_to_pass:          0
% 3.88/0.99  
% 3.88/0.99  ------ Superposition
% 3.88/0.99  
% 3.88/0.99  sup_time_total:                         0.
% 3.88/0.99  sup_time_generating:                    0.
% 3.88/0.99  sup_time_sim_full:                      0.
% 3.88/0.99  sup_time_sim_immed:                     0.
% 3.88/0.99  
% 3.88/0.99  sup_num_of_clauses:                     289
% 3.88/0.99  sup_num_in_active:                      85
% 3.88/0.99  sup_num_in_passive:                     204
% 3.88/0.99  sup_num_of_loops:                       158
% 3.88/0.99  sup_fw_superposition:                   255
% 3.88/0.99  sup_bw_superposition:                   209
% 3.88/0.99  sup_immediate_simplified:               82
% 3.88/0.99  sup_given_eliminated:                   1
% 3.88/0.99  comparisons_done:                       0
% 3.88/0.99  comparisons_avoided:                    0
% 3.88/0.99  
% 3.88/0.99  ------ Simplifications
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  sim_fw_subset_subsumed:                 45
% 3.88/0.99  sim_bw_subset_subsumed:                 6
% 3.88/0.99  sim_fw_subsumed:                        20
% 3.88/0.99  sim_bw_subsumed:                        7
% 3.88/0.99  sim_fw_subsumption_res:                 15
% 3.88/0.99  sim_bw_subsumption_res:                 0
% 3.88/0.99  sim_tautology_del:                      9
% 3.88/0.99  sim_eq_tautology_del:                   3
% 3.88/0.99  sim_eq_res_simp:                        0
% 3.88/0.99  sim_fw_demodulated:                     2
% 3.88/0.99  sim_bw_demodulated:                     74
% 3.88/0.99  sim_light_normalised:                   8
% 3.88/0.99  sim_joinable_taut:                      0
% 3.88/0.99  sim_joinable_simp:                      0
% 3.88/0.99  sim_ac_normalised:                      0
% 3.88/0.99  sim_smt_subsumption:                    0
% 3.88/0.99  
%------------------------------------------------------------------------------
