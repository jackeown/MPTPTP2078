%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:51 EST 2020

% Result     : Theorem 7.27s
% Output     : CNFRefutation 7.27s
% Verified   : 
% Statistics : Number of formulae       :  270 (14600 expanded)
%              Number of clauses        :  176 (3442 expanded)
%              Number of leaves         :   21 (4290 expanded)
%              Depth                    :   30
%              Number of atoms          : 1211 (164918 expanded)
%              Number of equality atoms :  421 (19811 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f50])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f65,plain,(
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

fof(f64,plain,(
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

fof(f63,plain,(
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

fof(f62,plain,
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

fof(f66,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f61,f65,f64,f63,f62])).

fof(f109,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f66])).

fof(f113,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f66])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f112,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f66])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f31])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f110,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f102,plain,(
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
    inference(cnf_transformation,[],[f59])).

fof(f127,plain,(
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
    inference(equality_resolution,[],[f102])).

fof(f103,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f104,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f105,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f106,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f111,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f66])).

fof(f108,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f66])).

fof(f114,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f97,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f43,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f98,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f96,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f99,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f126,plain,(
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
    inference(equality_resolution,[],[f99])).

fof(f101,plain,(
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
    inference(cnf_transformation,[],[f59])).

fof(f128,plain,(
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
    inference(equality_resolution,[],[f101])).

fof(f115,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f125,plain,(
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
    inference(equality_resolution,[],[f100])).

fof(f12,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f53])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f118,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f72])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f119,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f71])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2790,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_38,negated_conjecture,
    ( sK2 = sK3 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2845,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2790,c_38])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_10])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_625,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_621,c_11])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_625])).

cnf(c_2782,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_3309,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2845,c_2782])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2793,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2812,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7161,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2793,c_2812])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2813,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7487,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0,sK3) = k1_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7161,c_2813])).

cnf(c_8060,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3309,c_7487])).

cnf(c_26,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2804,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | v1_funct_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9749,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8060,c_2804])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_56,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

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
    inference(cnf_transformation,[],[f127])).

cnf(c_2797,plain,
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

cnf(c_5838,plain,
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
    inference(superposition,[status(thm)],[c_2793,c_2797])).

cnf(c_48,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_49,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_50,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_51,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_52,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_57,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2789,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_2840,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2789,c_38])).

cnf(c_37,negated_conjecture,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2794,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2901,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2794,c_38])).

cnf(c_30,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3156,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3157,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3156])).

cnf(c_31,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3177,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_3178,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3177])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3375,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3376,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3375])).

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
    inference(cnf_transformation,[],[f126])).

cnf(c_3346,plain,
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
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_3702,plain,
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
    inference(instantiation,[status(thm)],[c_3346])).

cnf(c_4203,plain,
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
    inference(instantiation,[status(thm)],[c_3702])).

cnf(c_4204,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4203])).

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
    inference(cnf_transformation,[],[f128])).

cnf(c_2796,plain,
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

cnf(c_5051,plain,
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
    inference(superposition,[status(thm)],[c_2793,c_2796])).

cnf(c_36,negated_conjecture,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2795,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2906,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2795,c_38])).

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
    inference(cnf_transformation,[],[f125])).

cnf(c_3336,plain,
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
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_3648,plain,
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
    inference(instantiation,[status(thm)],[c_3336])).

cnf(c_4171,plain,
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
    inference(instantiation,[status(thm)],[c_3648])).

cnf(c_4172,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4171])).

cnf(c_5307,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5051,c_49,c_50,c_51,c_52,c_56,c_57,c_2840,c_2845,c_2906,c_3157,c_3178,c_3376,c_4172])).

cnf(c_5308,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5307])).

cnf(c_6121,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5838,c_49,c_50,c_51,c_52,c_56,c_57,c_2840,c_2845,c_2901,c_3157,c_3178,c_3376,c_4204,c_5308])).

cnf(c_6122,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6121])).

cnf(c_7494,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7161,c_6122])).

cnf(c_24448,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9749,c_56,c_3309,c_7494])).

cnf(c_24449,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_24448])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2806,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8560,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2793,c_2806])).

cnf(c_5935,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2793,c_2813])).

cnf(c_8596,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8560,c_5935])).

cnf(c_8635,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8596])).

cnf(c_13860,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8596,c_40,c_8635])).

cnf(c_13861,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_13860])).

cnf(c_8561,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2845,c_2806])).

cnf(c_5936,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2845,c_2813])).

cnf(c_8589,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8561,c_5936])).

cnf(c_9994,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8589,c_2840])).

cnf(c_9995,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_9994])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2814,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4385,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2845,c_2814])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2818,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6010,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4385,c_2818])).

cnf(c_10021,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9995,c_6010])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_10100,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10021,c_3])).

cnf(c_4539,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4540,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4539])).

cnf(c_4542,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4540])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7374,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_7377,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7374])).

cnf(c_10450,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10100,c_4542,c_7377])).

cnf(c_10451,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_10450])).

cnf(c_10454,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0) = sK3
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_9995,c_10451])).

cnf(c_10535,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10454,c_3])).

cnf(c_2792,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_10605,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10535,c_2792])).

cnf(c_13915,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13861,c_10605])).

cnf(c_4541,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3))
    | r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_4539])).

cnf(c_4731,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4733,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4731])).

cnf(c_4384,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2793,c_2814])).

cnf(c_13921,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13861,c_4384])).

cnf(c_13940,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13921,c_3])).

cnf(c_14798,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13940])).

cnf(c_15642,plain,
    ( sK3 = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13915,c_4541,c_4733,c_7374,c_14798])).

cnf(c_15643,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_15642])).

cnf(c_15715,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15643,c_2792])).

cnf(c_10607,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10535,c_2840])).

cnf(c_7163,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_2812])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3408,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_2782])).

cnf(c_7208,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7163,c_3408])).

cnf(c_7221,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7208,c_6122])).

cnf(c_9134,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7221,c_3309,c_7494])).

cnf(c_15705,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15643,c_9134])).

cnf(c_16550,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15715,c_10607,c_15705])).

cnf(c_24452,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24449,c_16550])).

cnf(c_2816,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_24455,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_24452,c_2816])).

cnf(c_3670,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2793,c_2782])).

cnf(c_7162,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2845,c_2812])).

cnf(c_7402,plain,
    ( k1_relset_1(u1_struct_0(sK0),X0,sK3) = k1_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7162,c_2813])).

cnf(c_7959,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3670,c_7402])).

cnf(c_9748,plain,
    ( u1_struct_0(sK0) != k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7959,c_2804])).

cnf(c_58,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3230,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_3231,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3230])).

cnf(c_2798,plain,
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

cnf(c_6515,plain,
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
    inference(superposition,[status(thm)],[c_2793,c_2798])).

cnf(c_3153,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3154,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3153])).

cnf(c_3174,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_3175,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3174])).

cnf(c_3371,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3372,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3371])).

cnf(c_3356,plain,
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
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_3742,plain,
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
    inference(instantiation,[status(thm)],[c_3356])).

cnf(c_4227,plain,
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
    inference(instantiation,[status(thm)],[c_3742])).

cnf(c_4228,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4227])).

cnf(c_3366,plain,
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
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3782,plain,
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
    inference(instantiation,[status(thm)],[c_3366])).

cnf(c_4301,plain,
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
    inference(instantiation,[status(thm)],[c_3782])).

cnf(c_4302,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4301])).

cnf(c_3658,plain,
    ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_3336])).

cnf(c_4933,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3658])).

cnf(c_4934,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4933])).

cnf(c_6864,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6515,c_49,c_50,c_51,c_52,c_56,c_57,c_58,c_2840,c_2845,c_2906,c_2901,c_3154,c_3175,c_3372,c_4228,c_4302,c_4934])).

cnf(c_6865,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6864])).

cnf(c_6868,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6865,c_49,c_50,c_51,c_52,c_56,c_57,c_58,c_2840,c_2845,c_2901,c_3154,c_3175,c_3372,c_4302,c_4934])).

cnf(c_7407,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7162,c_6868])).

cnf(c_24366,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | u1_struct_0(sK0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9748,c_56,c_58,c_3231,c_7407])).

cnf(c_24367,plain,
    ( u1_struct_0(sK0) != k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_24366])).

cnf(c_24370,plain,
    ( u1_struct_0(sK0) != k1_relat_1(k1_xboole_0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24367,c_16550])).

cnf(c_24373,plain,
    ( u1_struct_0(sK0) != k1_relat_1(k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_24370,c_2816])).

cnf(c_13924,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13861,c_2792])).

cnf(c_16557,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16550,c_13924])).

cnf(c_16584,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_16550,c_9995])).

cnf(c_16594,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16550,c_9134])).

cnf(c_18857,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16584,c_16594])).

cnf(c_23782,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_16557,c_18857])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24455,c_24373,c_23782])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:32:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.27/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.27/1.48  
% 7.27/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.27/1.48  
% 7.27/1.48  ------  iProver source info
% 7.27/1.48  
% 7.27/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.27/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.27/1.48  git: non_committed_changes: false
% 7.27/1.48  git: last_make_outside_of_git: false
% 7.27/1.48  
% 7.27/1.48  ------ 
% 7.27/1.48  
% 7.27/1.48  ------ Input Options
% 7.27/1.48  
% 7.27/1.48  --out_options                           all
% 7.27/1.48  --tptp_safe_out                         true
% 7.27/1.48  --problem_path                          ""
% 7.27/1.48  --include_path                          ""
% 7.27/1.48  --clausifier                            res/vclausify_rel
% 7.27/1.48  --clausifier_options                    --mode clausify
% 7.27/1.48  --stdin                                 false
% 7.27/1.48  --stats_out                             all
% 7.27/1.48  
% 7.27/1.48  ------ General Options
% 7.27/1.48  
% 7.27/1.48  --fof                                   false
% 7.27/1.48  --time_out_real                         305.
% 7.27/1.48  --time_out_virtual                      -1.
% 7.27/1.48  --symbol_type_check                     false
% 7.27/1.48  --clausify_out                          false
% 7.27/1.48  --sig_cnt_out                           false
% 7.27/1.48  --trig_cnt_out                          false
% 7.27/1.48  --trig_cnt_out_tolerance                1.
% 7.27/1.48  --trig_cnt_out_sk_spl                   false
% 7.27/1.48  --abstr_cl_out                          false
% 7.27/1.48  
% 7.27/1.48  ------ Global Options
% 7.27/1.48  
% 7.27/1.48  --schedule                              default
% 7.27/1.48  --add_important_lit                     false
% 7.27/1.48  --prop_solver_per_cl                    1000
% 7.27/1.48  --min_unsat_core                        false
% 7.27/1.48  --soft_assumptions                      false
% 7.27/1.48  --soft_lemma_size                       3
% 7.27/1.48  --prop_impl_unit_size                   0
% 7.27/1.48  --prop_impl_unit                        []
% 7.27/1.48  --share_sel_clauses                     true
% 7.27/1.48  --reset_solvers                         false
% 7.27/1.48  --bc_imp_inh                            [conj_cone]
% 7.27/1.48  --conj_cone_tolerance                   3.
% 7.27/1.48  --extra_neg_conj                        none
% 7.27/1.48  --large_theory_mode                     true
% 7.27/1.48  --prolific_symb_bound                   200
% 7.27/1.48  --lt_threshold                          2000
% 7.27/1.48  --clause_weak_htbl                      true
% 7.27/1.48  --gc_record_bc_elim                     false
% 7.27/1.48  
% 7.27/1.48  ------ Preprocessing Options
% 7.27/1.48  
% 7.27/1.48  --preprocessing_flag                    true
% 7.27/1.48  --time_out_prep_mult                    0.1
% 7.27/1.48  --splitting_mode                        input
% 7.27/1.48  --splitting_grd                         true
% 7.27/1.48  --splitting_cvd                         false
% 7.27/1.48  --splitting_cvd_svl                     false
% 7.27/1.48  --splitting_nvd                         32
% 7.27/1.48  --sub_typing                            true
% 7.27/1.48  --prep_gs_sim                           true
% 7.27/1.48  --prep_unflatten                        true
% 7.27/1.48  --prep_res_sim                          true
% 7.27/1.48  --prep_upred                            true
% 7.27/1.48  --prep_sem_filter                       exhaustive
% 7.27/1.48  --prep_sem_filter_out                   false
% 7.27/1.48  --pred_elim                             true
% 7.27/1.48  --res_sim_input                         true
% 7.27/1.48  --eq_ax_congr_red                       true
% 7.27/1.48  --pure_diseq_elim                       true
% 7.27/1.48  --brand_transform                       false
% 7.27/1.48  --non_eq_to_eq                          false
% 7.27/1.48  --prep_def_merge                        true
% 7.27/1.48  --prep_def_merge_prop_impl              false
% 7.27/1.48  --prep_def_merge_mbd                    true
% 7.27/1.48  --prep_def_merge_tr_red                 false
% 7.27/1.48  --prep_def_merge_tr_cl                  false
% 7.27/1.48  --smt_preprocessing                     true
% 7.27/1.48  --smt_ac_axioms                         fast
% 7.27/1.48  --preprocessed_out                      false
% 7.27/1.48  --preprocessed_stats                    false
% 7.27/1.48  
% 7.27/1.48  ------ Abstraction refinement Options
% 7.27/1.48  
% 7.27/1.48  --abstr_ref                             []
% 7.27/1.48  --abstr_ref_prep                        false
% 7.27/1.48  --abstr_ref_until_sat                   false
% 7.27/1.48  --abstr_ref_sig_restrict                funpre
% 7.27/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.27/1.48  --abstr_ref_under                       []
% 7.27/1.48  
% 7.27/1.48  ------ SAT Options
% 7.27/1.48  
% 7.27/1.48  --sat_mode                              false
% 7.27/1.48  --sat_fm_restart_options                ""
% 7.27/1.48  --sat_gr_def                            false
% 7.27/1.48  --sat_epr_types                         true
% 7.27/1.48  --sat_non_cyclic_types                  false
% 7.27/1.48  --sat_finite_models                     false
% 7.27/1.48  --sat_fm_lemmas                         false
% 7.27/1.48  --sat_fm_prep                           false
% 7.27/1.48  --sat_fm_uc_incr                        true
% 7.27/1.48  --sat_out_model                         small
% 7.27/1.48  --sat_out_clauses                       false
% 7.27/1.48  
% 7.27/1.48  ------ QBF Options
% 7.27/1.48  
% 7.27/1.48  --qbf_mode                              false
% 7.27/1.48  --qbf_elim_univ                         false
% 7.27/1.48  --qbf_dom_inst                          none
% 7.27/1.48  --qbf_dom_pre_inst                      false
% 7.27/1.48  --qbf_sk_in                             false
% 7.27/1.48  --qbf_pred_elim                         true
% 7.27/1.48  --qbf_split                             512
% 7.27/1.48  
% 7.27/1.48  ------ BMC1 Options
% 7.27/1.48  
% 7.27/1.48  --bmc1_incremental                      false
% 7.27/1.48  --bmc1_axioms                           reachable_all
% 7.27/1.48  --bmc1_min_bound                        0
% 7.27/1.48  --bmc1_max_bound                        -1
% 7.27/1.48  --bmc1_max_bound_default                -1
% 7.27/1.48  --bmc1_symbol_reachability              true
% 7.27/1.48  --bmc1_property_lemmas                  false
% 7.27/1.48  --bmc1_k_induction                      false
% 7.27/1.48  --bmc1_non_equiv_states                 false
% 7.27/1.48  --bmc1_deadlock                         false
% 7.27/1.48  --bmc1_ucm                              false
% 7.27/1.48  --bmc1_add_unsat_core                   none
% 7.27/1.48  --bmc1_unsat_core_children              false
% 7.27/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.27/1.48  --bmc1_out_stat                         full
% 7.27/1.48  --bmc1_ground_init                      false
% 7.27/1.48  --bmc1_pre_inst_next_state              false
% 7.27/1.48  --bmc1_pre_inst_state                   false
% 7.27/1.48  --bmc1_pre_inst_reach_state             false
% 7.27/1.48  --bmc1_out_unsat_core                   false
% 7.27/1.48  --bmc1_aig_witness_out                  false
% 7.27/1.48  --bmc1_verbose                          false
% 7.27/1.48  --bmc1_dump_clauses_tptp                false
% 7.27/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.27/1.48  --bmc1_dump_file                        -
% 7.27/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.27/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.27/1.48  --bmc1_ucm_extend_mode                  1
% 7.27/1.48  --bmc1_ucm_init_mode                    2
% 7.27/1.48  --bmc1_ucm_cone_mode                    none
% 7.27/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.27/1.48  --bmc1_ucm_relax_model                  4
% 7.27/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.27/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.27/1.48  --bmc1_ucm_layered_model                none
% 7.27/1.48  --bmc1_ucm_max_lemma_size               10
% 7.27/1.48  
% 7.27/1.48  ------ AIG Options
% 7.27/1.48  
% 7.27/1.48  --aig_mode                              false
% 7.27/1.48  
% 7.27/1.48  ------ Instantiation Options
% 7.27/1.48  
% 7.27/1.48  --instantiation_flag                    true
% 7.27/1.48  --inst_sos_flag                         false
% 7.27/1.48  --inst_sos_phase                        true
% 7.27/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.27/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.27/1.48  --inst_lit_sel_side                     num_symb
% 7.27/1.48  --inst_solver_per_active                1400
% 7.27/1.48  --inst_solver_calls_frac                1.
% 7.27/1.48  --inst_passive_queue_type               priority_queues
% 7.27/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.27/1.48  --inst_passive_queues_freq              [25;2]
% 7.27/1.48  --inst_dismatching                      true
% 7.27/1.48  --inst_eager_unprocessed_to_passive     true
% 7.27/1.48  --inst_prop_sim_given                   true
% 7.27/1.48  --inst_prop_sim_new                     false
% 7.27/1.48  --inst_subs_new                         false
% 7.27/1.48  --inst_eq_res_simp                      false
% 7.27/1.48  --inst_subs_given                       false
% 7.27/1.48  --inst_orphan_elimination               true
% 7.27/1.48  --inst_learning_loop_flag               true
% 7.27/1.48  --inst_learning_start                   3000
% 7.27/1.48  --inst_learning_factor                  2
% 7.27/1.48  --inst_start_prop_sim_after_learn       3
% 7.27/1.48  --inst_sel_renew                        solver
% 7.27/1.48  --inst_lit_activity_flag                true
% 7.27/1.48  --inst_restr_to_given                   false
% 7.27/1.48  --inst_activity_threshold               500
% 7.27/1.48  --inst_out_proof                        true
% 7.27/1.48  
% 7.27/1.48  ------ Resolution Options
% 7.27/1.48  
% 7.27/1.48  --resolution_flag                       true
% 7.27/1.48  --res_lit_sel                           adaptive
% 7.27/1.48  --res_lit_sel_side                      none
% 7.27/1.48  --res_ordering                          kbo
% 7.27/1.48  --res_to_prop_solver                    active
% 7.27/1.48  --res_prop_simpl_new                    false
% 7.27/1.48  --res_prop_simpl_given                  true
% 7.27/1.48  --res_passive_queue_type                priority_queues
% 7.27/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.27/1.48  --res_passive_queues_freq               [15;5]
% 7.27/1.48  --res_forward_subs                      full
% 7.27/1.48  --res_backward_subs                     full
% 7.27/1.48  --res_forward_subs_resolution           true
% 7.27/1.48  --res_backward_subs_resolution          true
% 7.27/1.48  --res_orphan_elimination                true
% 7.27/1.48  --res_time_limit                        2.
% 7.27/1.48  --res_out_proof                         true
% 7.27/1.48  
% 7.27/1.48  ------ Superposition Options
% 7.27/1.48  
% 7.27/1.48  --superposition_flag                    true
% 7.27/1.48  --sup_passive_queue_type                priority_queues
% 7.27/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.27/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.27/1.48  --demod_completeness_check              fast
% 7.27/1.48  --demod_use_ground                      true
% 7.27/1.48  --sup_to_prop_solver                    passive
% 7.27/1.48  --sup_prop_simpl_new                    true
% 7.27/1.48  --sup_prop_simpl_given                  true
% 7.27/1.48  --sup_fun_splitting                     false
% 7.27/1.48  --sup_smt_interval                      50000
% 7.27/1.48  
% 7.27/1.48  ------ Superposition Simplification Setup
% 7.27/1.48  
% 7.27/1.48  --sup_indices_passive                   []
% 7.27/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.27/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.27/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.27/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.27/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.27/1.48  --sup_full_bw                           [BwDemod]
% 7.27/1.48  --sup_immed_triv                        [TrivRules]
% 7.27/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.27/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.27/1.48  --sup_immed_bw_main                     []
% 7.27/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.27/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.27/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.27/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.27/1.48  
% 7.27/1.48  ------ Combination Options
% 7.27/1.48  
% 7.27/1.48  --comb_res_mult                         3
% 7.27/1.48  --comb_sup_mult                         2
% 7.27/1.48  --comb_inst_mult                        10
% 7.27/1.48  
% 7.27/1.48  ------ Debug Options
% 7.27/1.48  
% 7.27/1.48  --dbg_backtrace                         false
% 7.27/1.48  --dbg_dump_prop_clauses                 false
% 7.27/1.48  --dbg_dump_prop_clauses_file            -
% 7.27/1.48  --dbg_out_stat                          false
% 7.27/1.48  ------ Parsing...
% 7.27/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.27/1.48  
% 7.27/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.27/1.48  
% 7.27/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.27/1.48  
% 7.27/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.27/1.48  ------ Proving...
% 7.27/1.48  ------ Problem Properties 
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  clauses                                 41
% 7.27/1.48  conjectures                             13
% 7.27/1.48  EPR                                     9
% 7.27/1.48  Horn                                    35
% 7.27/1.48  unary                                   16
% 7.27/1.48  binary                                  8
% 7.27/1.48  lits                                    120
% 7.27/1.48  lits eq                                 19
% 7.27/1.48  fd_pure                                 0
% 7.27/1.48  fd_pseudo                               0
% 7.27/1.48  fd_cond                                 4
% 7.27/1.48  fd_pseudo_cond                          1
% 7.27/1.48  AC symbols                              0
% 7.27/1.48  
% 7.27/1.48  ------ Schedule dynamic 5 is on 
% 7.27/1.48  
% 7.27/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  ------ 
% 7.27/1.48  Current options:
% 7.27/1.48  ------ 
% 7.27/1.48  
% 7.27/1.48  ------ Input Options
% 7.27/1.48  
% 7.27/1.48  --out_options                           all
% 7.27/1.48  --tptp_safe_out                         true
% 7.27/1.48  --problem_path                          ""
% 7.27/1.48  --include_path                          ""
% 7.27/1.48  --clausifier                            res/vclausify_rel
% 7.27/1.48  --clausifier_options                    --mode clausify
% 7.27/1.48  --stdin                                 false
% 7.27/1.48  --stats_out                             all
% 7.27/1.48  
% 7.27/1.48  ------ General Options
% 7.27/1.48  
% 7.27/1.48  --fof                                   false
% 7.27/1.48  --time_out_real                         305.
% 7.27/1.48  --time_out_virtual                      -1.
% 7.27/1.48  --symbol_type_check                     false
% 7.27/1.48  --clausify_out                          false
% 7.27/1.48  --sig_cnt_out                           false
% 7.27/1.48  --trig_cnt_out                          false
% 7.27/1.48  --trig_cnt_out_tolerance                1.
% 7.27/1.48  --trig_cnt_out_sk_spl                   false
% 7.27/1.48  --abstr_cl_out                          false
% 7.27/1.48  
% 7.27/1.48  ------ Global Options
% 7.27/1.48  
% 7.27/1.48  --schedule                              default
% 7.27/1.48  --add_important_lit                     false
% 7.27/1.48  --prop_solver_per_cl                    1000
% 7.27/1.48  --min_unsat_core                        false
% 7.27/1.48  --soft_assumptions                      false
% 7.27/1.48  --soft_lemma_size                       3
% 7.27/1.48  --prop_impl_unit_size                   0
% 7.27/1.48  --prop_impl_unit                        []
% 7.27/1.48  --share_sel_clauses                     true
% 7.27/1.48  --reset_solvers                         false
% 7.27/1.48  --bc_imp_inh                            [conj_cone]
% 7.27/1.48  --conj_cone_tolerance                   3.
% 7.27/1.48  --extra_neg_conj                        none
% 7.27/1.48  --large_theory_mode                     true
% 7.27/1.48  --prolific_symb_bound                   200
% 7.27/1.48  --lt_threshold                          2000
% 7.27/1.48  --clause_weak_htbl                      true
% 7.27/1.48  --gc_record_bc_elim                     false
% 7.27/1.48  
% 7.27/1.48  ------ Preprocessing Options
% 7.27/1.48  
% 7.27/1.48  --preprocessing_flag                    true
% 7.27/1.48  --time_out_prep_mult                    0.1
% 7.27/1.48  --splitting_mode                        input
% 7.27/1.48  --splitting_grd                         true
% 7.27/1.48  --splitting_cvd                         false
% 7.27/1.48  --splitting_cvd_svl                     false
% 7.27/1.48  --splitting_nvd                         32
% 7.27/1.48  --sub_typing                            true
% 7.27/1.48  --prep_gs_sim                           true
% 7.27/1.48  --prep_unflatten                        true
% 7.27/1.48  --prep_res_sim                          true
% 7.27/1.48  --prep_upred                            true
% 7.27/1.48  --prep_sem_filter                       exhaustive
% 7.27/1.48  --prep_sem_filter_out                   false
% 7.27/1.48  --pred_elim                             true
% 7.27/1.48  --res_sim_input                         true
% 7.27/1.48  --eq_ax_congr_red                       true
% 7.27/1.48  --pure_diseq_elim                       true
% 7.27/1.48  --brand_transform                       false
% 7.27/1.48  --non_eq_to_eq                          false
% 7.27/1.48  --prep_def_merge                        true
% 7.27/1.48  --prep_def_merge_prop_impl              false
% 7.27/1.48  --prep_def_merge_mbd                    true
% 7.27/1.48  --prep_def_merge_tr_red                 false
% 7.27/1.48  --prep_def_merge_tr_cl                  false
% 7.27/1.48  --smt_preprocessing                     true
% 7.27/1.48  --smt_ac_axioms                         fast
% 7.27/1.48  --preprocessed_out                      false
% 7.27/1.48  --preprocessed_stats                    false
% 7.27/1.48  
% 7.27/1.48  ------ Abstraction refinement Options
% 7.27/1.48  
% 7.27/1.48  --abstr_ref                             []
% 7.27/1.48  --abstr_ref_prep                        false
% 7.27/1.48  --abstr_ref_until_sat                   false
% 7.27/1.48  --abstr_ref_sig_restrict                funpre
% 7.27/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.27/1.48  --abstr_ref_under                       []
% 7.27/1.48  
% 7.27/1.48  ------ SAT Options
% 7.27/1.48  
% 7.27/1.48  --sat_mode                              false
% 7.27/1.48  --sat_fm_restart_options                ""
% 7.27/1.48  --sat_gr_def                            false
% 7.27/1.48  --sat_epr_types                         true
% 7.27/1.48  --sat_non_cyclic_types                  false
% 7.27/1.48  --sat_finite_models                     false
% 7.27/1.48  --sat_fm_lemmas                         false
% 7.27/1.48  --sat_fm_prep                           false
% 7.27/1.48  --sat_fm_uc_incr                        true
% 7.27/1.48  --sat_out_model                         small
% 7.27/1.48  --sat_out_clauses                       false
% 7.27/1.48  
% 7.27/1.48  ------ QBF Options
% 7.27/1.48  
% 7.27/1.48  --qbf_mode                              false
% 7.27/1.48  --qbf_elim_univ                         false
% 7.27/1.48  --qbf_dom_inst                          none
% 7.27/1.48  --qbf_dom_pre_inst                      false
% 7.27/1.48  --qbf_sk_in                             false
% 7.27/1.48  --qbf_pred_elim                         true
% 7.27/1.48  --qbf_split                             512
% 7.27/1.48  
% 7.27/1.48  ------ BMC1 Options
% 7.27/1.48  
% 7.27/1.48  --bmc1_incremental                      false
% 7.27/1.48  --bmc1_axioms                           reachable_all
% 7.27/1.48  --bmc1_min_bound                        0
% 7.27/1.48  --bmc1_max_bound                        -1
% 7.27/1.48  --bmc1_max_bound_default                -1
% 7.27/1.48  --bmc1_symbol_reachability              true
% 7.27/1.48  --bmc1_property_lemmas                  false
% 7.27/1.48  --bmc1_k_induction                      false
% 7.27/1.48  --bmc1_non_equiv_states                 false
% 7.27/1.48  --bmc1_deadlock                         false
% 7.27/1.48  --bmc1_ucm                              false
% 7.27/1.48  --bmc1_add_unsat_core                   none
% 7.27/1.48  --bmc1_unsat_core_children              false
% 7.27/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.27/1.48  --bmc1_out_stat                         full
% 7.27/1.48  --bmc1_ground_init                      false
% 7.27/1.48  --bmc1_pre_inst_next_state              false
% 7.27/1.48  --bmc1_pre_inst_state                   false
% 7.27/1.48  --bmc1_pre_inst_reach_state             false
% 7.27/1.48  --bmc1_out_unsat_core                   false
% 7.27/1.48  --bmc1_aig_witness_out                  false
% 7.27/1.48  --bmc1_verbose                          false
% 7.27/1.48  --bmc1_dump_clauses_tptp                false
% 7.27/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.27/1.48  --bmc1_dump_file                        -
% 7.27/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.27/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.27/1.48  --bmc1_ucm_extend_mode                  1
% 7.27/1.48  --bmc1_ucm_init_mode                    2
% 7.27/1.48  --bmc1_ucm_cone_mode                    none
% 7.27/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.27/1.48  --bmc1_ucm_relax_model                  4
% 7.27/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.27/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.27/1.48  --bmc1_ucm_layered_model                none
% 7.27/1.48  --bmc1_ucm_max_lemma_size               10
% 7.27/1.48  
% 7.27/1.48  ------ AIG Options
% 7.27/1.48  
% 7.27/1.48  --aig_mode                              false
% 7.27/1.48  
% 7.27/1.48  ------ Instantiation Options
% 7.27/1.48  
% 7.27/1.48  --instantiation_flag                    true
% 7.27/1.48  --inst_sos_flag                         false
% 7.27/1.48  --inst_sos_phase                        true
% 7.27/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.27/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.27/1.48  --inst_lit_sel_side                     none
% 7.27/1.48  --inst_solver_per_active                1400
% 7.27/1.48  --inst_solver_calls_frac                1.
% 7.27/1.48  --inst_passive_queue_type               priority_queues
% 7.27/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.27/1.48  --inst_passive_queues_freq              [25;2]
% 7.27/1.48  --inst_dismatching                      true
% 7.27/1.48  --inst_eager_unprocessed_to_passive     true
% 7.27/1.48  --inst_prop_sim_given                   true
% 7.27/1.48  --inst_prop_sim_new                     false
% 7.27/1.48  --inst_subs_new                         false
% 7.27/1.48  --inst_eq_res_simp                      false
% 7.27/1.48  --inst_subs_given                       false
% 7.27/1.48  --inst_orphan_elimination               true
% 7.27/1.48  --inst_learning_loop_flag               true
% 7.27/1.48  --inst_learning_start                   3000
% 7.27/1.48  --inst_learning_factor                  2
% 7.27/1.48  --inst_start_prop_sim_after_learn       3
% 7.27/1.48  --inst_sel_renew                        solver
% 7.27/1.48  --inst_lit_activity_flag                true
% 7.27/1.48  --inst_restr_to_given                   false
% 7.27/1.48  --inst_activity_threshold               500
% 7.27/1.48  --inst_out_proof                        true
% 7.27/1.48  
% 7.27/1.48  ------ Resolution Options
% 7.27/1.48  
% 7.27/1.48  --resolution_flag                       false
% 7.27/1.48  --res_lit_sel                           adaptive
% 7.27/1.48  --res_lit_sel_side                      none
% 7.27/1.48  --res_ordering                          kbo
% 7.27/1.48  --res_to_prop_solver                    active
% 7.27/1.48  --res_prop_simpl_new                    false
% 7.27/1.48  --res_prop_simpl_given                  true
% 7.27/1.48  --res_passive_queue_type                priority_queues
% 7.27/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.27/1.48  --res_passive_queues_freq               [15;5]
% 7.27/1.48  --res_forward_subs                      full
% 7.27/1.48  --res_backward_subs                     full
% 7.27/1.48  --res_forward_subs_resolution           true
% 7.27/1.48  --res_backward_subs_resolution          true
% 7.27/1.48  --res_orphan_elimination                true
% 7.27/1.48  --res_time_limit                        2.
% 7.27/1.48  --res_out_proof                         true
% 7.27/1.48  
% 7.27/1.48  ------ Superposition Options
% 7.27/1.48  
% 7.27/1.48  --superposition_flag                    true
% 7.27/1.48  --sup_passive_queue_type                priority_queues
% 7.27/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.27/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.27/1.48  --demod_completeness_check              fast
% 7.27/1.48  --demod_use_ground                      true
% 7.27/1.48  --sup_to_prop_solver                    passive
% 7.27/1.48  --sup_prop_simpl_new                    true
% 7.27/1.48  --sup_prop_simpl_given                  true
% 7.27/1.48  --sup_fun_splitting                     false
% 7.27/1.48  --sup_smt_interval                      50000
% 7.27/1.48  
% 7.27/1.48  ------ Superposition Simplification Setup
% 7.27/1.48  
% 7.27/1.48  --sup_indices_passive                   []
% 7.27/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.27/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.27/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.27/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.27/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.27/1.48  --sup_full_bw                           [BwDemod]
% 7.27/1.48  --sup_immed_triv                        [TrivRules]
% 7.27/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.27/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.27/1.48  --sup_immed_bw_main                     []
% 7.27/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.27/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.27/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.27/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.27/1.48  
% 7.27/1.48  ------ Combination Options
% 7.27/1.48  
% 7.27/1.48  --comb_res_mult                         3
% 7.27/1.48  --comb_sup_mult                         2
% 7.27/1.48  --comb_inst_mult                        10
% 7.27/1.48  
% 7.27/1.48  ------ Debug Options
% 7.27/1.48  
% 7.27/1.48  --dbg_backtrace                         false
% 7.27/1.48  --dbg_dump_prop_clauses                 false
% 7.27/1.48  --dbg_dump_prop_clauses_file            -
% 7.27/1.48  --dbg_out_stat                          false
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  ------ Proving...
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  % SZS status Theorem for theBenchmark.p
% 7.27/1.48  
% 7.27/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.27/1.48  
% 7.27/1.48  fof(f21,conjecture,(
% 7.27/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f22,negated_conjecture,(
% 7.27/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.27/1.48    inference(negated_conjecture,[],[f21])).
% 7.27/1.48  
% 7.27/1.48  fof(f49,plain,(
% 7.27/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.27/1.48    inference(ennf_transformation,[],[f22])).
% 7.27/1.48  
% 7.27/1.48  fof(f50,plain,(
% 7.27/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.27/1.48    inference(flattening,[],[f49])).
% 7.27/1.48  
% 7.27/1.48  fof(f60,plain,(
% 7.27/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.27/1.48    inference(nnf_transformation,[],[f50])).
% 7.27/1.48  
% 7.27/1.48  fof(f61,plain,(
% 7.27/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.27/1.48    inference(flattening,[],[f60])).
% 7.27/1.48  
% 7.27/1.48  fof(f65,plain,(
% 7.27/1.48    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK3 = X2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK3))) )),
% 7.27/1.48    introduced(choice_axiom,[])).
% 7.27/1.48  
% 7.27/1.48  fof(f64,plain,(
% 7.27/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 7.27/1.48    introduced(choice_axiom,[])).
% 7.27/1.48  
% 7.27/1.48  fof(f63,plain,(
% 7.27/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,X0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,X0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 7.27/1.48    introduced(choice_axiom,[])).
% 7.27/1.48  
% 7.27/1.48  fof(f62,plain,(
% 7.27/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.27/1.48    introduced(choice_axiom,[])).
% 7.27/1.48  
% 7.27/1.48  fof(f66,plain,(
% 7.27/1.48    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.27/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f61,f65,f64,f63,f62])).
% 7.27/1.48  
% 7.27/1.48  fof(f109,plain,(
% 7.27/1.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 7.27/1.48    inference(cnf_transformation,[],[f66])).
% 7.27/1.48  
% 7.27/1.48  fof(f113,plain,(
% 7.27/1.48    sK2 = sK3),
% 7.27/1.48    inference(cnf_transformation,[],[f66])).
% 7.27/1.48  
% 7.27/1.48  fof(f8,axiom,(
% 7.27/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f25,plain,(
% 7.27/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.27/1.48    inference(pure_predicate_removal,[],[f8])).
% 7.27/1.48  
% 7.27/1.48  fof(f29,plain,(
% 7.27/1.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.27/1.48    inference(ennf_transformation,[],[f25])).
% 7.27/1.48  
% 7.27/1.48  fof(f79,plain,(
% 7.27/1.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.27/1.48    inference(cnf_transformation,[],[f29])).
% 7.27/1.48  
% 7.27/1.48  fof(f6,axiom,(
% 7.27/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f27,plain,(
% 7.27/1.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.27/1.48    inference(ennf_transformation,[],[f6])).
% 7.27/1.48  
% 7.27/1.48  fof(f56,plain,(
% 7.27/1.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.27/1.48    inference(nnf_transformation,[],[f27])).
% 7.27/1.48  
% 7.27/1.48  fof(f76,plain,(
% 7.27/1.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f56])).
% 7.27/1.48  
% 7.27/1.48  fof(f7,axiom,(
% 7.27/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f28,plain,(
% 7.27/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.27/1.48    inference(ennf_transformation,[],[f7])).
% 7.27/1.48  
% 7.27/1.48  fof(f78,plain,(
% 7.27/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.27/1.48    inference(cnf_transformation,[],[f28])).
% 7.27/1.48  
% 7.27/1.48  fof(f112,plain,(
% 7.27/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 7.27/1.48    inference(cnf_transformation,[],[f66])).
% 7.27/1.48  
% 7.27/1.48  fof(f10,axiom,(
% 7.27/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f31,plain,(
% 7.27/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 7.27/1.48    inference(ennf_transformation,[],[f10])).
% 7.27/1.48  
% 7.27/1.48  fof(f32,plain,(
% 7.27/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 7.27/1.48    inference(flattening,[],[f31])).
% 7.27/1.48  
% 7.27/1.48  fof(f81,plain,(
% 7.27/1.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 7.27/1.48    inference(cnf_transformation,[],[f32])).
% 7.27/1.48  
% 7.27/1.48  fof(f9,axiom,(
% 7.27/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f30,plain,(
% 7.27/1.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.27/1.48    inference(ennf_transformation,[],[f9])).
% 7.27/1.48  
% 7.27/1.48  fof(f80,plain,(
% 7.27/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.27/1.48    inference(cnf_transformation,[],[f30])).
% 7.27/1.48  
% 7.27/1.48  fof(f14,axiom,(
% 7.27/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f37,plain,(
% 7.27/1.48    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.27/1.48    inference(ennf_transformation,[],[f14])).
% 7.27/1.48  
% 7.27/1.48  fof(f38,plain,(
% 7.27/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.27/1.48    inference(flattening,[],[f37])).
% 7.27/1.48  
% 7.27/1.48  fof(f93,plain,(
% 7.27/1.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f38])).
% 7.27/1.48  
% 7.27/1.48  fof(f110,plain,(
% 7.27/1.48    v1_funct_1(sK3)),
% 7.27/1.48    inference(cnf_transformation,[],[f66])).
% 7.27/1.48  
% 7.27/1.48  fof(f20,axiom,(
% 7.27/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f47,plain,(
% 7.27/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.27/1.48    inference(ennf_transformation,[],[f20])).
% 7.27/1.48  
% 7.27/1.48  fof(f48,plain,(
% 7.27/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.27/1.48    inference(flattening,[],[f47])).
% 7.27/1.48  
% 7.27/1.48  fof(f59,plain,(
% 7.27/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.27/1.48    inference(nnf_transformation,[],[f48])).
% 7.27/1.48  
% 7.27/1.48  fof(f102,plain,(
% 7.27/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f59])).
% 7.27/1.48  
% 7.27/1.48  fof(f127,plain,(
% 7.27/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.27/1.48    inference(equality_resolution,[],[f102])).
% 7.27/1.48  
% 7.27/1.48  fof(f103,plain,(
% 7.27/1.48    v2_pre_topc(sK0)),
% 7.27/1.48    inference(cnf_transformation,[],[f66])).
% 7.27/1.48  
% 7.27/1.48  fof(f104,plain,(
% 7.27/1.48    l1_pre_topc(sK0)),
% 7.27/1.48    inference(cnf_transformation,[],[f66])).
% 7.27/1.48  
% 7.27/1.48  fof(f105,plain,(
% 7.27/1.48    v2_pre_topc(sK1)),
% 7.27/1.48    inference(cnf_transformation,[],[f66])).
% 7.27/1.48  
% 7.27/1.48  fof(f106,plain,(
% 7.27/1.48    l1_pre_topc(sK1)),
% 7.27/1.48    inference(cnf_transformation,[],[f66])).
% 7.27/1.48  
% 7.27/1.48  fof(f111,plain,(
% 7.27/1.48    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 7.27/1.48    inference(cnf_transformation,[],[f66])).
% 7.27/1.48  
% 7.27/1.48  fof(f108,plain,(
% 7.27/1.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 7.27/1.48    inference(cnf_transformation,[],[f66])).
% 7.27/1.48  
% 7.27/1.48  fof(f114,plain,(
% 7.27/1.48    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 7.27/1.48    inference(cnf_transformation,[],[f66])).
% 7.27/1.48  
% 7.27/1.48  fof(f17,axiom,(
% 7.27/1.48    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f42,plain,(
% 7.27/1.48    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.27/1.48    inference(ennf_transformation,[],[f17])).
% 7.27/1.48  
% 7.27/1.48  fof(f97,plain,(
% 7.27/1.48    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f42])).
% 7.27/1.48  
% 7.27/1.48  fof(f18,axiom,(
% 7.27/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f23,plain,(
% 7.27/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 7.27/1.48    inference(pure_predicate_removal,[],[f18])).
% 7.27/1.48  
% 7.27/1.48  fof(f43,plain,(
% 7.27/1.48    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.27/1.48    inference(ennf_transformation,[],[f23])).
% 7.27/1.48  
% 7.27/1.48  fof(f44,plain,(
% 7.27/1.48    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.27/1.48    inference(flattening,[],[f43])).
% 7.27/1.48  
% 7.27/1.48  fof(f98,plain,(
% 7.27/1.48    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f44])).
% 7.27/1.48  
% 7.27/1.48  fof(f16,axiom,(
% 7.27/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f24,plain,(
% 7.27/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 7.27/1.48    inference(pure_predicate_removal,[],[f16])).
% 7.27/1.48  
% 7.27/1.48  fof(f41,plain,(
% 7.27/1.48    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.27/1.48    inference(ennf_transformation,[],[f24])).
% 7.27/1.48  
% 7.27/1.48  fof(f96,plain,(
% 7.27/1.48    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.27/1.48    inference(cnf_transformation,[],[f41])).
% 7.27/1.48  
% 7.27/1.48  fof(f19,axiom,(
% 7.27/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f45,plain,(
% 7.27/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.27/1.48    inference(ennf_transformation,[],[f19])).
% 7.27/1.48  
% 7.27/1.48  fof(f46,plain,(
% 7.27/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.27/1.48    inference(flattening,[],[f45])).
% 7.27/1.48  
% 7.27/1.48  fof(f58,plain,(
% 7.27/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.27/1.48    inference(nnf_transformation,[],[f46])).
% 7.27/1.48  
% 7.27/1.48  fof(f99,plain,(
% 7.27/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f58])).
% 7.27/1.48  
% 7.27/1.48  fof(f126,plain,(
% 7.27/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.27/1.48    inference(equality_resolution,[],[f99])).
% 7.27/1.48  
% 7.27/1.48  fof(f101,plain,(
% 7.27/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f59])).
% 7.27/1.48  
% 7.27/1.48  fof(f128,plain,(
% 7.27/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.27/1.48    inference(equality_resolution,[],[f101])).
% 7.27/1.48  
% 7.27/1.48  fof(f115,plain,(
% 7.27/1.48    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 7.27/1.48    inference(cnf_transformation,[],[f66])).
% 7.27/1.48  
% 7.27/1.48  fof(f100,plain,(
% 7.27/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f58])).
% 7.27/1.48  
% 7.27/1.48  fof(f125,plain,(
% 7.27/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.27/1.48    inference(equality_resolution,[],[f100])).
% 7.27/1.48  
% 7.27/1.48  fof(f12,axiom,(
% 7.27/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f35,plain,(
% 7.27/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.27/1.48    inference(ennf_transformation,[],[f12])).
% 7.27/1.48  
% 7.27/1.48  fof(f36,plain,(
% 7.27/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.27/1.48    inference(flattening,[],[f35])).
% 7.27/1.48  
% 7.27/1.48  fof(f57,plain,(
% 7.27/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.27/1.48    inference(nnf_transformation,[],[f36])).
% 7.27/1.48  
% 7.27/1.48  fof(f84,plain,(
% 7.27/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.27/1.48    inference(cnf_transformation,[],[f57])).
% 7.27/1.48  
% 7.27/1.48  fof(f4,axiom,(
% 7.27/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f55,plain,(
% 7.27/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.27/1.48    inference(nnf_transformation,[],[f4])).
% 7.27/1.48  
% 7.27/1.48  fof(f74,plain,(
% 7.27/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.27/1.48    inference(cnf_transformation,[],[f55])).
% 7.27/1.48  
% 7.27/1.48  fof(f1,axiom,(
% 7.27/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f51,plain,(
% 7.27/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.27/1.48    inference(nnf_transformation,[],[f1])).
% 7.27/1.48  
% 7.27/1.48  fof(f52,plain,(
% 7.27/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.27/1.48    inference(flattening,[],[f51])).
% 7.27/1.48  
% 7.27/1.48  fof(f69,plain,(
% 7.27/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.27/1.48    inference(cnf_transformation,[],[f52])).
% 7.27/1.48  
% 7.27/1.48  fof(f2,axiom,(
% 7.27/1.48    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f53,plain,(
% 7.27/1.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.27/1.48    inference(nnf_transformation,[],[f2])).
% 7.27/1.48  
% 7.27/1.48  fof(f54,plain,(
% 7.27/1.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.27/1.48    inference(flattening,[],[f53])).
% 7.27/1.48  
% 7.27/1.48  fof(f72,plain,(
% 7.27/1.48    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 7.27/1.48    inference(cnf_transformation,[],[f54])).
% 7.27/1.48  
% 7.27/1.48  fof(f118,plain,(
% 7.27/1.48    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.27/1.48    inference(equality_resolution,[],[f72])).
% 7.27/1.48  
% 7.27/1.48  fof(f3,axiom,(
% 7.27/1.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.27/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.48  
% 7.27/1.48  fof(f73,plain,(
% 7.27/1.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.27/1.48    inference(cnf_transformation,[],[f3])).
% 7.27/1.48  
% 7.27/1.48  fof(f71,plain,(
% 7.27/1.48    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 7.27/1.48    inference(cnf_transformation,[],[f54])).
% 7.27/1.48  
% 7.27/1.48  fof(f119,plain,(
% 7.27/1.48    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 7.27/1.48    inference(equality_resolution,[],[f71])).
% 7.27/1.48  
% 7.27/1.48  cnf(c_42,negated_conjecture,
% 7.27/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 7.27/1.48      inference(cnf_transformation,[],[f109]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2790,plain,
% 7.27/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_38,negated_conjecture,
% 7.27/1.48      ( sK2 = sK3 ),
% 7.27/1.48      inference(cnf_transformation,[],[f113]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2845,plain,
% 7.27/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.27/1.48      inference(light_normalisation,[status(thm)],[c_2790,c_38]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_12,plain,
% 7.27/1.48      ( v5_relat_1(X0,X1)
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.27/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_10,plain,
% 7.27/1.48      ( ~ v5_relat_1(X0,X1)
% 7.27/1.48      | r1_tarski(k2_relat_1(X0),X1)
% 7.27/1.48      | ~ v1_relat_1(X0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_621,plain,
% 7.27/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | r1_tarski(k2_relat_1(X0),X2)
% 7.27/1.48      | ~ v1_relat_1(X0) ),
% 7.27/1.48      inference(resolution,[status(thm)],[c_12,c_10]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_11,plain,
% 7.27/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | v1_relat_1(X0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_625,plain,
% 7.27/1.48      ( r1_tarski(k2_relat_1(X0),X2)
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_621,c_11]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_626,plain,
% 7.27/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_625]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2782,plain,
% 7.27/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.27/1.48      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3309,plain,
% 7.27/1.48      ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2845,c_2782]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_39,negated_conjecture,
% 7.27/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
% 7.27/1.48      inference(cnf_transformation,[],[f112]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2793,plain,
% 7.27/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_14,plain,
% 7.27/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.27/1.48      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 7.27/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2812,plain,
% 7.27/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.27/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 7.27/1.48      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_7161,plain,
% 7.27/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0))) = iProver_top
% 7.27/1.48      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2793,c_2812]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_13,plain,
% 7.27/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2813,plain,
% 7.27/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.27/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_7487,plain,
% 7.27/1.48      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0,sK3) = k1_relat_1(sK3)
% 7.27/1.48      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_7161,c_2813]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_8060,plain,
% 7.27/1.48      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_3309,c_7487]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_26,plain,
% 7.27/1.48      ( v1_funct_2(X0,X1,X2)
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | ~ v1_funct_1(X0)
% 7.27/1.48      | k1_relset_1(X1,X2,X0) != X1 ),
% 7.27/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2804,plain,
% 7.27/1.48      ( k1_relset_1(X0,X1,X2) != X0
% 7.27/1.48      | v1_funct_2(X2,X0,X1) = iProver_top
% 7.27/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.27/1.48      | v1_funct_1(X2) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_9749,plain,
% 7.27/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3)
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) = iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.27/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_8060,c_2804]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_41,negated_conjecture,
% 7.27/1.48      ( v1_funct_1(sK3) ),
% 7.27/1.48      inference(cnf_transformation,[],[f110]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_56,plain,
% 7.27/1.48      ( v1_funct_1(sK3) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_34,plain,
% 7.27/1.48      ( v5_pre_topc(X0,X1,X2)
% 7.27/1.48      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.27/1.48      | ~ v2_pre_topc(X1)
% 7.27/1.48      | ~ v2_pre_topc(X2)
% 7.27/1.48      | ~ l1_pre_topc(X1)
% 7.27/1.48      | ~ l1_pre_topc(X2)
% 7.27/1.48      | ~ v1_funct_1(X0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f127]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2797,plain,
% 7.27/1.48      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 7.27/1.48      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 7.27/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.27/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.27/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.27/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.27/1.48      | v2_pre_topc(X1) != iProver_top
% 7.27/1.48      | v2_pre_topc(X2) != iProver_top
% 7.27/1.48      | l1_pre_topc(X1) != iProver_top
% 7.27/1.48      | l1_pre_topc(X2) != iProver_top
% 7.27/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_5838,plain,
% 7.27/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.27/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.27/1.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.27/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.27/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.27/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.27/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2793,c_2797]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_48,negated_conjecture,
% 7.27/1.48      ( v2_pre_topc(sK0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f103]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_49,plain,
% 7.27/1.48      ( v2_pre_topc(sK0) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_47,negated_conjecture,
% 7.27/1.48      ( l1_pre_topc(sK0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f104]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_50,plain,
% 7.27/1.48      ( l1_pre_topc(sK0) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_46,negated_conjecture,
% 7.27/1.48      ( v2_pre_topc(sK1) ),
% 7.27/1.48      inference(cnf_transformation,[],[f105]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_51,plain,
% 7.27/1.48      ( v2_pre_topc(sK1) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_45,negated_conjecture,
% 7.27/1.48      ( l1_pre_topc(sK1) ),
% 7.27/1.48      inference(cnf_transformation,[],[f106]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_52,plain,
% 7.27/1.48      ( l1_pre_topc(sK1) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_40,negated_conjecture,
% 7.27/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
% 7.27/1.48      inference(cnf_transformation,[],[f111]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_57,plain,
% 7.27/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_43,negated_conjecture,
% 7.27/1.48      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 7.27/1.48      inference(cnf_transformation,[],[f108]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2789,plain,
% 7.27/1.48      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2840,plain,
% 7.27/1.48      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.27/1.48      inference(light_normalisation,[status(thm)],[c_2789,c_38]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_37,negated_conjecture,
% 7.27/1.48      ( v5_pre_topc(sK2,sK0,sK1)
% 7.27/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.27/1.48      inference(cnf_transformation,[],[f114]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2794,plain,
% 7.27/1.48      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
% 7.27/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2901,plain,
% 7.27/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.27/1.48      | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
% 7.27/1.48      inference(light_normalisation,[status(thm)],[c_2794,c_38]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_30,plain,
% 7.27/1.48      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.27/1.48      | ~ l1_pre_topc(X0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f97]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3156,plain,
% 7.27/1.48      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.27/1.48      | ~ l1_pre_topc(sK0) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_30]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3157,plain,
% 7.27/1.48      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 7.27/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_3156]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_31,plain,
% 7.27/1.48      ( ~ v2_pre_topc(X0)
% 7.27/1.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.27/1.48      | ~ l1_pre_topc(X0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f98]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3177,plain,
% 7.27/1.48      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(sK0) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_31]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3178,plain,
% 7.27/1.48      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 7.27/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.27/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_3177]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_29,plain,
% 7.27/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.27/1.48      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 7.27/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3375,plain,
% 7.27/1.48      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.27/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_29]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3376,plain,
% 7.27/1.48      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 7.27/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_3375]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_33,plain,
% 7.27/1.48      ( ~ v5_pre_topc(X0,X1,X2)
% 7.27/1.48      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.27/1.48      | ~ v2_pre_topc(X1)
% 7.27/1.48      | ~ v2_pre_topc(X2)
% 7.27/1.48      | ~ l1_pre_topc(X1)
% 7.27/1.48      | ~ l1_pre_topc(X2)
% 7.27/1.48      | ~ v1_funct_1(X0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f126]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3346,plain,
% 7.27/1.48      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
% 7.27/1.48      | ~ v5_pre_topc(X0,sK0,X1)
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 7.27/1.48      | ~ v2_pre_topc(X1)
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(X1)
% 7.27/1.48      | ~ l1_pre_topc(sK0)
% 7.27/1.48      | ~ v1_funct_1(X0) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_33]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3702,plain,
% 7.27/1.48      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 7.27/1.48      | ~ v5_pre_topc(X0,sK0,sK1)
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.27/1.48      | ~ v2_pre_topc(sK1)
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(sK1)
% 7.27/1.48      | ~ l1_pre_topc(sK0)
% 7.27/1.48      | ~ v1_funct_1(X0) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_3346]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4203,plain,
% 7.27/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 7.27/1.48      | ~ v5_pre_topc(sK3,sK0,sK1)
% 7.27/1.48      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 7.27/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.27/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 7.27/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.27/1.48      | ~ v2_pre_topc(sK1)
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(sK1)
% 7.27/1.48      | ~ l1_pre_topc(sK0)
% 7.27/1.48      | ~ v1_funct_1(sK3) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_3702]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4204,plain,
% 7.27/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 7.27/1.48      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.27/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.27/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.27/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.27/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.27/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_4203]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_35,plain,
% 7.27/1.48      ( ~ v5_pre_topc(X0,X1,X2)
% 7.27/1.48      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.27/1.48      | ~ v2_pre_topc(X1)
% 7.27/1.48      | ~ v2_pre_topc(X2)
% 7.27/1.48      | ~ l1_pre_topc(X1)
% 7.27/1.48      | ~ l1_pre_topc(X2)
% 7.27/1.48      | ~ v1_funct_1(X0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f128]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2796,plain,
% 7.27/1.48      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.27/1.48      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 7.27/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.27/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.27/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.27/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.27/1.48      | v2_pre_topc(X1) != iProver_top
% 7.27/1.48      | v2_pre_topc(X2) != iProver_top
% 7.27/1.48      | l1_pre_topc(X1) != iProver_top
% 7.27/1.48      | l1_pre_topc(X2) != iProver_top
% 7.27/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_5051,plain,
% 7.27/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.27/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.27/1.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.27/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.27/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.27/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.27/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2793,c_2796]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_36,negated_conjecture,
% 7.27/1.48      ( ~ v5_pre_topc(sK2,sK0,sK1)
% 7.27/1.48      | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.27/1.48      inference(cnf_transformation,[],[f115]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2795,plain,
% 7.27/1.48      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
% 7.27/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2906,plain,
% 7.27/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.27/1.48      | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
% 7.27/1.48      inference(light_normalisation,[status(thm)],[c_2795,c_38]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_32,plain,
% 7.27/1.48      ( v5_pre_topc(X0,X1,X2)
% 7.27/1.48      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.27/1.48      | ~ v2_pre_topc(X1)
% 7.27/1.48      | ~ v2_pre_topc(X2)
% 7.27/1.48      | ~ l1_pre_topc(X1)
% 7.27/1.48      | ~ l1_pre_topc(X2)
% 7.27/1.48      | ~ v1_funct_1(X0) ),
% 7.27/1.48      inference(cnf_transformation,[],[f125]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3336,plain,
% 7.27/1.48      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
% 7.27/1.48      | v5_pre_topc(X0,sK0,X1)
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 7.27/1.48      | ~ v2_pre_topc(X1)
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(X1)
% 7.27/1.48      | ~ l1_pre_topc(sK0)
% 7.27/1.48      | ~ v1_funct_1(X0) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_32]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3648,plain,
% 7.27/1.48      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 7.27/1.48      | v5_pre_topc(X0,sK0,sK1)
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.27/1.48      | ~ v2_pre_topc(sK1)
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(sK1)
% 7.27/1.48      | ~ l1_pre_topc(sK0)
% 7.27/1.48      | ~ v1_funct_1(X0) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_3336]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4171,plain,
% 7.27/1.48      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 7.27/1.48      | v5_pre_topc(sK3,sK0,sK1)
% 7.27/1.48      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 7.27/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.27/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 7.27/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.27/1.48      | ~ v2_pre_topc(sK1)
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(sK1)
% 7.27/1.48      | ~ l1_pre_topc(sK0)
% 7.27/1.48      | ~ v1_funct_1(sK3) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_3648]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4172,plain,
% 7.27/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 7.27/1.48      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.27/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.27/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.27/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.27/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.27/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_4171]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_5307,plain,
% 7.27/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.27/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_5051,c_49,c_50,c_51,c_52,c_56,c_57,c_2840,c_2845,
% 7.27/1.48                 c_2906,c_3157,c_3178,c_3376,c_4172]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_5308,plain,
% 7.27/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_5307]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_6121,plain,
% 7.27/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_5838,c_49,c_50,c_51,c_52,c_56,c_57,c_2840,c_2845,
% 7.27/1.48                 c_2901,c_3157,c_3178,c_3376,c_4204,c_5308]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_6122,plain,
% 7.27/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_6121]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_7494,plain,
% 7.27/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.27/1.48      | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_7161,c_6122]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_24448,plain,
% 7.27/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.27/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3) ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_9749,c_56,c_3309,c_7494]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_24449,plain,
% 7.27/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3)
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_24448]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_22,plain,
% 7.27/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.27/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.27/1.48      | k1_xboole_0 = X2 ),
% 7.27/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2806,plain,
% 7.27/1.48      ( k1_relset_1(X0,X1,X2) = X0
% 7.27/1.48      | k1_xboole_0 = X1
% 7.27/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.27/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_8560,plain,
% 7.27/1.48      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 7.27/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2793,c_2806]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_5935,plain,
% 7.27/1.48      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2793,c_2813]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_8596,plain,
% 7.27/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 7.27/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 7.27/1.48      inference(light_normalisation,[status(thm)],[c_8560,c_5935]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_8635,plain,
% 7.27/1.48      ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.27/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 7.27/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.27/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_8596]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_13860,plain,
% 7.27/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.27/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0 ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_8596,c_40,c_8635]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_13861,plain,
% 7.27/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 7.27/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_13860]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_8561,plain,
% 7.27/1.48      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = u1_struct_0(sK0)
% 7.27/1.48      | u1_struct_0(sK1) = k1_xboole_0
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2845,c_2806]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_5936,plain,
% 7.27/1.48      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2845,c_2813]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_8589,plain,
% 7.27/1.48      ( u1_struct_0(sK1) = k1_xboole_0
% 7.27/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 7.27/1.48      inference(light_normalisation,[status(thm)],[c_8561,c_5936]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_9994,plain,
% 7.27/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.27/1.48      | u1_struct_0(sK1) = k1_xboole_0 ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_8589,c_2840]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_9995,plain,
% 7.27/1.48      ( u1_struct_0(sK1) = k1_xboole_0
% 7.27/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_9994]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_8,plain,
% 7.27/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.27/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2814,plain,
% 7.27/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.27/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4385,plain,
% 7.27/1.48      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2845,c_2814]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_0,plain,
% 7.27/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.27/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2818,plain,
% 7.27/1.48      ( X0 = X1
% 7.27/1.48      | r1_tarski(X0,X1) != iProver_top
% 7.27/1.48      | r1_tarski(X1,X0) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_6010,plain,
% 7.27/1.48      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 7.27/1.48      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK3) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_4385,c_2818]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_10021,plain,
% 7.27/1.48      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 7.27/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.27/1.48      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),sK3) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_9995,c_6010]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3,plain,
% 7.27/1.48      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.27/1.48      inference(cnf_transformation,[],[f118]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_10100,plain,
% 7.27/1.48      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 7.27/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.27/1.48      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_10021,c_3]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4539,plain,
% 7.27/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4540,plain,
% 7.27/1.48      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 7.27/1.48      | r1_tarski(X0,sK3) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_4539]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4542,plain,
% 7.27/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 7.27/1.48      | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_4540]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_6,plain,
% 7.27/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.27/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_7374,plain,
% 7.27/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_7377,plain,
% 7.27/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_7374]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_10450,plain,
% 7.27/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.27/1.48      | k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3 ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_10100,c_4542,c_7377]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_10451,plain,
% 7.27/1.48      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 7.27/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_10450]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_10454,plain,
% 7.27/1.48      ( k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0) = sK3
% 7.27/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_9995,c_10451]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_10535,plain,
% 7.27/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3) | sK3 = k1_xboole_0 ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_10454,c_3]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2792,plain,
% 7.27/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_10605,plain,
% 7.27/1.48      ( sK3 = k1_xboole_0
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_10535,c_2792]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_13915,plain,
% 7.27/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.27/1.48      | sK3 = k1_xboole_0
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_13861,c_10605]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4541,plain,
% 7.27/1.48      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3))
% 7.27/1.48      | r1_tarski(k1_xboole_0,sK3) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_4539]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4731,plain,
% 7.27/1.48      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4733,plain,
% 7.27/1.48      ( ~ r1_tarski(sK3,k1_xboole_0)
% 7.27/1.48      | ~ r1_tarski(k1_xboole_0,sK3)
% 7.27/1.48      | sK3 = k1_xboole_0 ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_4731]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4384,plain,
% 7.27/1.48      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2793,c_2814]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_13921,plain,
% 7.27/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.27/1.48      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_13861,c_4384]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_13940,plain,
% 7.27/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.27/1.48      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_13921,c_3]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_14798,plain,
% 7.27/1.48      ( r1_tarski(sK3,k1_xboole_0)
% 7.27/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.27/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_13940]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_15642,plain,
% 7.27/1.48      ( sK3 = k1_xboole_0
% 7.27/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_13915,c_4541,c_4733,c_7374,c_14798]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_15643,plain,
% 7.27/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.27/1.48      | sK3 = k1_xboole_0 ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_15642]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_15715,plain,
% 7.27/1.48      ( sK3 = k1_xboole_0
% 7.27/1.48      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_15643,c_2792]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_10607,plain,
% 7.27/1.48      ( sK3 = k1_xboole_0
% 7.27/1.48      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_10535,c_2840]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_7163,plain,
% 7.27/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.27/1.48      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.27/1.48      | r1_tarski(k2_relat_1(X0),X2) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_3,c_2812]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4,plain,
% 7.27/1.48      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.27/1.48      inference(cnf_transformation,[],[f119]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3408,plain,
% 7.27/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.27/1.48      | r1_tarski(k2_relat_1(X0),X1) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_4,c_2782]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_7208,plain,
% 7.27/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.27/1.48      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.27/1.48      inference(forward_subsumption_resolution,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_7163,c_3408]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_7221,plain,
% 7.27/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_7208,c_6122]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_9134,plain,
% 7.27/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_7221,c_3309,c_7494]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_15705,plain,
% 7.27/1.48      ( sK3 = k1_xboole_0
% 7.27/1.48      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_15643,c_9134]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_16550,plain,
% 7.27/1.48      ( sK3 = k1_xboole_0 ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_15715,c_10607,c_15705]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_24452,plain,
% 7.27/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0)
% 7.27/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 7.27/1.48      inference(light_normalisation,[status(thm)],[c_24449,c_16550]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2816,plain,
% 7.27/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_24455,plain,
% 7.27/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0) ),
% 7.27/1.48      inference(forward_subsumption_resolution,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_24452,c_2816]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3670,plain,
% 7.27/1.48      ( r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2793,c_2782]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_7162,plain,
% 7.27/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) = iProver_top
% 7.27/1.48      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2845,c_2812]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_7402,plain,
% 7.27/1.48      ( k1_relset_1(u1_struct_0(sK0),X0,sK3) = k1_relat_1(sK3)
% 7.27/1.48      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_7162,c_2813]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_7959,plain,
% 7.27/1.48      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_3670,c_7402]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_9748,plain,
% 7.27/1.48      ( u1_struct_0(sK0) != k1_relat_1(sK3)
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.27/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_7959,c_2804]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_58,plain,
% 7.27/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3230,plain,
% 7.27/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.27/1.48      | r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_626]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3231,plain,
% 7.27/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.27/1.48      | r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_3230]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_2798,plain,
% 7.27/1.48      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.27/1.48      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 7.27/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.27/1.48      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 7.27/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.27/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 7.27/1.48      | v2_pre_topc(X1) != iProver_top
% 7.27/1.48      | v2_pre_topc(X2) != iProver_top
% 7.27/1.48      | l1_pre_topc(X1) != iProver_top
% 7.27/1.48      | l1_pre_topc(X2) != iProver_top
% 7.27/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_6515,plain,
% 7.27/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.27/1.48      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.27/1.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.27/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.27/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.27/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.27/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_2793,c_2798]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3153,plain,
% 7.27/1.48      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.27/1.48      | ~ l1_pre_topc(sK1) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_30]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3154,plain,
% 7.27/1.48      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 7.27/1.48      | l1_pre_topc(sK1) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_3153]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3174,plain,
% 7.27/1.48      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.27/1.48      | ~ v2_pre_topc(sK1)
% 7.27/1.48      | ~ l1_pre_topc(sK1) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_31]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3175,plain,
% 7.27/1.48      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.27/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.27/1.48      | l1_pre_topc(sK1) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_3174]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3371,plain,
% 7.27/1.48      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.27/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_29]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3372,plain,
% 7.27/1.48      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 7.27/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_3371]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3356,plain,
% 7.27/1.48      ( v5_pre_topc(X0,sK0,X1)
% 7.27/1.48      | ~ v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 7.27/1.48      | ~ v2_pre_topc(X1)
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(X1)
% 7.27/1.48      | ~ l1_pre_topc(sK0)
% 7.27/1.48      | ~ v1_funct_1(X0) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_34]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3742,plain,
% 7.27/1.48      ( ~ v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.27/1.48      | v5_pre_topc(X0,sK0,sK1)
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.27/1.48      | ~ v2_pre_topc(sK1)
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(sK1)
% 7.27/1.48      | ~ l1_pre_topc(sK0)
% 7.27/1.48      | ~ v1_funct_1(X0) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_3356]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4227,plain,
% 7.27/1.48      ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.27/1.48      | v5_pre_topc(sK3,sK0,sK1)
% 7.27/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.27/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.27/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.27/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.27/1.48      | ~ v2_pre_topc(sK1)
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(sK1)
% 7.27/1.48      | ~ l1_pre_topc(sK0)
% 7.27/1.48      | ~ v1_funct_1(sK3) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_3742]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4228,plain,
% 7.27/1.48      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.27/1.48      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.27/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.27/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.27/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.27/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.27/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_4227]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3366,plain,
% 7.27/1.48      ( ~ v5_pre_topc(X0,sK0,X1)
% 7.27/1.48      | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 7.27/1.48      | ~ v2_pre_topc(X1)
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(X1)
% 7.27/1.48      | ~ l1_pre_topc(sK0)
% 7.27/1.48      | ~ v1_funct_1(X0) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_35]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3782,plain,
% 7.27/1.48      ( v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.27/1.48      | ~ v5_pre_topc(X0,sK0,sK1)
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.27/1.48      | ~ v2_pre_topc(sK1)
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(sK1)
% 7.27/1.48      | ~ l1_pre_topc(sK0)
% 7.27/1.48      | ~ v1_funct_1(X0) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_3366]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4301,plain,
% 7.27/1.48      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.27/1.48      | ~ v5_pre_topc(sK3,sK0,sK1)
% 7.27/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.27/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.27/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.27/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.27/1.48      | ~ v2_pre_topc(sK1)
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(sK1)
% 7.27/1.48      | ~ l1_pre_topc(sK0)
% 7.27/1.48      | ~ v1_funct_1(sK3) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_3782]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4302,plain,
% 7.27/1.48      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.27/1.48      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.27/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.27/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.27/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.27/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.27/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_4301]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_3658,plain,
% 7.27/1.48      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.27/1.48      | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.27/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.27/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.27/1.48      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.27/1.48      | ~ l1_pre_topc(sK0)
% 7.27/1.48      | ~ v1_funct_1(X0) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_3336]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4933,plain,
% 7.27/1.48      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.27/1.48      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.27/1.48      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.27/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.27/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.27/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.27/1.48      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.27/1.48      | ~ v2_pre_topc(sK0)
% 7.27/1.48      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.27/1.48      | ~ l1_pre_topc(sK0)
% 7.27/1.48      | ~ v1_funct_1(sK3) ),
% 7.27/1.48      inference(instantiation,[status(thm)],[c_3658]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_4934,plain,
% 7.27/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.27/1.48      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.27/1.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.27/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.27/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.27/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.27/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.27/1.48      inference(predicate_to_equality,[status(thm)],[c_4933]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_6864,plain,
% 7.27/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.27/1.48      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_6515,c_49,c_50,c_51,c_52,c_56,c_57,c_58,c_2840,c_2845,
% 7.27/1.48                 c_2906,c_2901,c_3154,c_3175,c_3372,c_4228,c_4302,c_4934]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_6865,plain,
% 7.27/1.48      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_6864]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_6868,plain,
% 7.27/1.48      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_6865,c_49,c_50,c_51,c_52,c_56,c_57,c_58,c_2840,c_2845,
% 7.27/1.48                 c_2901,c_3154,c_3175,c_3372,c_4302,c_4934]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_7407,plain,
% 7.27/1.48      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.27/1.48      | r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_7162,c_6868]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_24366,plain,
% 7.27/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.27/1.48      | u1_struct_0(sK0) != k1_relat_1(sK3) ),
% 7.27/1.48      inference(global_propositional_subsumption,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_9748,c_56,c_58,c_3231,c_7407]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_24367,plain,
% 7.27/1.48      ( u1_struct_0(sK0) != k1_relat_1(sK3)
% 7.27/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 7.27/1.48      inference(renaming,[status(thm)],[c_24366]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_24370,plain,
% 7.27/1.48      ( u1_struct_0(sK0) != k1_relat_1(k1_xboole_0)
% 7.27/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 7.27/1.48      inference(light_normalisation,[status(thm)],[c_24367,c_16550]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_24373,plain,
% 7.27/1.48      ( u1_struct_0(sK0) != k1_relat_1(k1_xboole_0) ),
% 7.27/1.48      inference(forward_subsumption_resolution,
% 7.27/1.48                [status(thm)],
% 7.27/1.48                [c_24370,c_2816]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_13924,plain,
% 7.27/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.27/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_13861,c_2792]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_16557,plain,
% 7.27/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
% 7.27/1.48      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_16550,c_13924]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_16584,plain,
% 7.27/1.48      ( u1_struct_0(sK1) = k1_xboole_0
% 7.27/1.48      | u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_16550,c_9995]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_16594,plain,
% 7.27/1.48      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 7.27/1.48      inference(demodulation,[status(thm)],[c_16550,c_9134]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_18857,plain,
% 7.27/1.48      ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
% 7.27/1.48      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_16584,c_16594]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(c_23782,plain,
% 7.27/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
% 7.27/1.48      | u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) ),
% 7.27/1.48      inference(superposition,[status(thm)],[c_16557,c_18857]) ).
% 7.27/1.48  
% 7.27/1.48  cnf(contradiction,plain,
% 7.27/1.48      ( $false ),
% 7.27/1.48      inference(minisat,[status(thm)],[c_24455,c_24373,c_23782]) ).
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.27/1.48  
% 7.27/1.48  ------                               Statistics
% 7.27/1.48  
% 7.27/1.48  ------ General
% 7.27/1.48  
% 7.27/1.48  abstr_ref_over_cycles:                  0
% 7.27/1.48  abstr_ref_under_cycles:                 0
% 7.27/1.48  gc_basic_clause_elim:                   0
% 7.27/1.48  forced_gc_time:                         0
% 7.27/1.48  parsing_time:                           0.012
% 7.27/1.48  unif_index_cands_time:                  0.
% 7.27/1.48  unif_index_add_time:                    0.
% 7.27/1.48  orderings_time:                         0.
% 7.27/1.48  out_proof_time:                         0.018
% 7.27/1.48  total_time:                             0.706
% 7.27/1.48  num_of_symbols:                         55
% 7.27/1.48  num_of_terms:                           16274
% 7.27/1.48  
% 7.27/1.48  ------ Preprocessing
% 7.27/1.48  
% 7.27/1.48  num_of_splits:                          0
% 7.27/1.48  num_of_split_atoms:                     0
% 7.27/1.48  num_of_reused_defs:                     0
% 7.27/1.48  num_eq_ax_congr_red:                    22
% 7.27/1.48  num_of_sem_filtered_clauses:            1
% 7.27/1.48  num_of_subtypes:                        0
% 7.27/1.48  monotx_restored_types:                  0
% 7.27/1.48  sat_num_of_epr_types:                   0
% 7.27/1.48  sat_num_of_non_cyclic_types:            0
% 7.27/1.48  sat_guarded_non_collapsed_types:        0
% 7.27/1.48  num_pure_diseq_elim:                    0
% 7.27/1.48  simp_replaced_by:                       0
% 7.27/1.48  res_preprocessed:                       199
% 7.27/1.48  prep_upred:                             0
% 7.27/1.48  prep_unflattend:                        26
% 7.27/1.48  smt_new_axioms:                         0
% 7.27/1.48  pred_elim_cands:                        7
% 7.27/1.48  pred_elim:                              3
% 7.27/1.48  pred_elim_cl:                           4
% 7.27/1.48  pred_elim_cycles:                       6
% 7.27/1.48  merged_defs:                            16
% 7.27/1.48  merged_defs_ncl:                        0
% 7.27/1.48  bin_hyper_res:                          16
% 7.27/1.48  prep_cycles:                            4
% 7.27/1.48  pred_elim_time:                         0.022
% 7.27/1.48  splitting_time:                         0.
% 7.27/1.48  sem_filter_time:                        0.
% 7.27/1.48  monotx_time:                            0.001
% 7.27/1.48  subtype_inf_time:                       0.
% 7.27/1.48  
% 7.27/1.48  ------ Problem properties
% 7.27/1.48  
% 7.27/1.48  clauses:                                41
% 7.27/1.48  conjectures:                            13
% 7.27/1.48  epr:                                    9
% 7.27/1.48  horn:                                   35
% 7.27/1.48  ground:                                 13
% 7.27/1.48  unary:                                  16
% 7.27/1.48  binary:                                 8
% 7.27/1.48  lits:                                   120
% 7.27/1.48  lits_eq:                                19
% 7.27/1.48  fd_pure:                                0
% 7.27/1.48  fd_pseudo:                              0
% 7.27/1.48  fd_cond:                                4
% 7.27/1.48  fd_pseudo_cond:                         1
% 7.27/1.48  ac_symbols:                             0
% 7.27/1.48  
% 7.27/1.48  ------ Propositional Solver
% 7.27/1.48  
% 7.27/1.48  prop_solver_calls:                      28
% 7.27/1.48  prop_fast_solver_calls:                 2943
% 7.27/1.48  smt_solver_calls:                       0
% 7.27/1.48  smt_fast_solver_calls:                  0
% 7.27/1.48  prop_num_of_clauses:                    7043
% 7.27/1.48  prop_preprocess_simplified:             16840
% 7.27/1.48  prop_fo_subsumed:                       175
% 7.27/1.48  prop_solver_time:                       0.
% 7.27/1.48  smt_solver_time:                        0.
% 7.27/1.48  smt_fast_solver_time:                   0.
% 7.27/1.48  prop_fast_solver_time:                  0.
% 7.27/1.48  prop_unsat_core_time:                   0.
% 7.27/1.48  
% 7.27/1.48  ------ QBF
% 7.27/1.48  
% 7.27/1.48  qbf_q_res:                              0
% 7.27/1.48  qbf_num_tautologies:                    0
% 7.27/1.48  qbf_prep_cycles:                        0
% 7.27/1.48  
% 7.27/1.48  ------ BMC1
% 7.27/1.48  
% 7.27/1.48  bmc1_current_bound:                     -1
% 7.27/1.48  bmc1_last_solved_bound:                 -1
% 7.27/1.48  bmc1_unsat_core_size:                   -1
% 7.27/1.48  bmc1_unsat_core_parents_size:           -1
% 7.27/1.48  bmc1_merge_next_fun:                    0
% 7.27/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.27/1.48  
% 7.27/1.48  ------ Instantiation
% 7.27/1.48  
% 7.27/1.48  inst_num_of_clauses:                    2054
% 7.27/1.48  inst_num_in_passive:                    1159
% 7.27/1.48  inst_num_in_active:                     763
% 7.27/1.48  inst_num_in_unprocessed:                132
% 7.27/1.48  inst_num_of_loops:                      1050
% 7.27/1.48  inst_num_of_learning_restarts:          0
% 7.27/1.48  inst_num_moves_active_passive:          286
% 7.27/1.48  inst_lit_activity:                      0
% 7.27/1.48  inst_lit_activity_moves:                0
% 7.27/1.48  inst_num_tautologies:                   0
% 7.27/1.48  inst_num_prop_implied:                  0
% 7.27/1.48  inst_num_existing_simplified:           0
% 7.27/1.48  inst_num_eq_res_simplified:             0
% 7.27/1.48  inst_num_child_elim:                    0
% 7.27/1.48  inst_num_of_dismatching_blockings:      274
% 7.27/1.48  inst_num_of_non_proper_insts:           1609
% 7.27/1.48  inst_num_of_duplicates:                 0
% 7.27/1.48  inst_inst_num_from_inst_to_res:         0
% 7.27/1.48  inst_dismatching_checking_time:         0.
% 7.27/1.48  
% 7.27/1.48  ------ Resolution
% 7.27/1.48  
% 7.27/1.48  res_num_of_clauses:                     0
% 7.27/1.48  res_num_in_passive:                     0
% 7.27/1.48  res_num_in_active:                      0
% 7.27/1.48  res_num_of_loops:                       203
% 7.27/1.48  res_forward_subset_subsumed:            81
% 7.27/1.48  res_backward_subset_subsumed:           0
% 7.27/1.48  res_forward_subsumed:                   0
% 7.27/1.48  res_backward_subsumed:                  0
% 7.27/1.48  res_forward_subsumption_resolution:     0
% 7.27/1.48  res_backward_subsumption_resolution:    0
% 7.27/1.48  res_clause_to_clause_subsumption:       1743
% 7.27/1.48  res_orphan_elimination:                 0
% 7.27/1.48  res_tautology_del:                      108
% 7.27/1.48  res_num_eq_res_simplified:              0
% 7.27/1.48  res_num_sel_changes:                    0
% 7.27/1.48  res_moves_from_active_to_pass:          0
% 7.27/1.48  
% 7.27/1.48  ------ Superposition
% 7.27/1.48  
% 7.27/1.48  sup_time_total:                         0.
% 7.27/1.48  sup_time_generating:                    0.
% 7.27/1.48  sup_time_sim_full:                      0.
% 7.27/1.48  sup_time_sim_immed:                     0.
% 7.27/1.48  
% 7.27/1.48  sup_num_of_clauses:                     413
% 7.27/1.48  sup_num_in_active:                      121
% 7.27/1.48  sup_num_in_passive:                     292
% 7.27/1.48  sup_num_of_loops:                       208
% 7.27/1.48  sup_fw_superposition:                   396
% 7.27/1.48  sup_bw_superposition:                   486
% 7.27/1.48  sup_immediate_simplified:               258
% 7.27/1.48  sup_given_eliminated:                   0
% 7.27/1.48  comparisons_done:                       0
% 7.27/1.48  comparisons_avoided:                    34
% 7.27/1.48  
% 7.27/1.48  ------ Simplifications
% 7.27/1.48  
% 7.27/1.48  
% 7.27/1.48  sim_fw_subset_subsumed:                 99
% 7.27/1.48  sim_bw_subset_subsumed:                 130
% 7.27/1.48  sim_fw_subsumed:                        71
% 7.27/1.48  sim_bw_subsumed:                        8
% 7.27/1.48  sim_fw_subsumption_res:                 30
% 7.27/1.48  sim_bw_subsumption_res:                 0
% 7.27/1.48  sim_tautology_del:                      25
% 7.27/1.48  sim_eq_tautology_del:                   24
% 7.27/1.48  sim_eq_res_simp:                        0
% 7.27/1.48  sim_fw_demodulated:                     73
% 7.27/1.48  sim_bw_demodulated:                     74
% 7.27/1.48  sim_light_normalised:                   67
% 7.27/1.48  sim_joinable_taut:                      0
% 7.27/1.48  sim_joinable_simp:                      0
% 7.27/1.48  sim_ac_normalised:                      0
% 7.27/1.48  sim_smt_subsumption:                    0
% 7.27/1.48  
%------------------------------------------------------------------------------
