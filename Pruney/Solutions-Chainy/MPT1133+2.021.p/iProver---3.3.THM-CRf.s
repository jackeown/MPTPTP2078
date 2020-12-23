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
% DateTime   : Thu Dec  3 12:11:52 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  258 (25967 expanded)
%              Number of clauses        :  162 (6306 expanded)
%              Number of leaves         :   22 (6859 expanded)
%              Depth                    :   34
%              Number of atoms          : 1294 (241719 expanded)
%              Number of equality atoms :  434 (28680 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f55])).

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
    inference(flattening,[],[f62])).

fof(f67,plain,(
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

fof(f66,plain,(
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

fof(f65,plain,(
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

fof(f64,plain,
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

fof(f68,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f63,f67,f66,f65,f64])).

fof(f110,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f68])).

fof(f114,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f68])).

fof(f16,axiom,(
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

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f111,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f68])).

fof(f109,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f68])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f113,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f68])).

fof(f112,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f68])).

fof(f21,axiom,(
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

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f53])).

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
    inference(cnf_transformation,[],[f61])).

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
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f105,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f106,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f107,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f115,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f99,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f97,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f46])).

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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f51])).

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
    inference(cnf_transformation,[],[f60])).

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
    inference(cnf_transformation,[],[f61])).

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
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

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
    inference(cnf_transformation,[],[f60])).

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

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f56])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f117,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f73])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2931,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_37,negated_conjecture,
    ( sK2 = sK3 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2978,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2931,c_37])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_22,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_564,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_13,c_22])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_564,c_22,c_13,c_12])).

cnf(c_569,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_568])).

cnf(c_629,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_27,c_569])).

cnf(c_633,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_27,c_12,c_564])).

cnf(c_634,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_633])).

cnf(c_2923,plain,
    ( k1_relat_1(X0) = X1
    | k1_xboole_0 = X2
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_4321,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2978,c_2923])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_653,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_16,c_569])).

cnf(c_655,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_653,c_22,c_16,c_13,c_12])).

cnf(c_656,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_655])).

cnf(c_2922,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_3426,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2978,c_2922])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_55,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2930,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_2975,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2930,c_37])).

cnf(c_3999,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3426,c_55,c_2975])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2952,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4447,plain,
    ( u1_struct_0(sK1) = X0
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3999,c_2952])).

cnf(c_4466,plain,
    ( ~ v1_xboole_0(X0)
    | u1_struct_0(sK1) = X0
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4447])).

cnf(c_4468,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4466])).

cnf(c_4526,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4321,c_0,c_4468])).

cnf(c_29,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2942,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_8,c_11])).

cnf(c_2924,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_5116,plain,
    ( m1_subset_1(X0,u1_pre_topc(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_pre_topc(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2942,c_2924])).

cnf(c_15220,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | m1_subset_1(X0,u1_pre_topc(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_pre_topc(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4526,c_5116])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2934,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4320,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2934,c_2923])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_4359,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4320])).

cnf(c_5029,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4320,c_40,c_39,c_4359])).

cnf(c_2933,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_5037,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5029,c_2933])).

cnf(c_33,plain,
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

cnf(c_2938,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6618,plain,
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
    inference(superposition,[status(thm)],[c_2934,c_2938])).

cnf(c_47,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_48,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_49,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_50,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_51,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_56,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_36,negated_conjecture,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2935,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3039,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2935,c_37])).

cnf(c_3274,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3275,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3274])).

cnf(c_30,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3297,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3298,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3297])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3913,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_3914,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3913])).

cnf(c_32,plain,
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

cnf(c_3405,plain,
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
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_3736,plain,
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
    inference(instantiation,[status(thm)],[c_3405])).

cnf(c_4293,plain,
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
    inference(instantiation,[status(thm)],[c_3736])).

cnf(c_4294,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4293])).

cnf(c_34,plain,
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

cnf(c_2937,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5782,plain,
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
    inference(superposition,[status(thm)],[c_2934,c_2937])).

cnf(c_35,negated_conjecture,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2936,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3044,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2936,c_37])).

cnf(c_31,plain,
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

cnf(c_3395,plain,
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
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_3696,plain,
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
    inference(instantiation,[status(thm)],[c_3395])).

cnf(c_4269,plain,
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
    inference(instantiation,[status(thm)],[c_3696])).

cnf(c_4270,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4269])).

cnf(c_6278,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5782,c_48,c_49,c_50,c_51,c_55,c_56,c_3044,c_2975,c_2978,c_3275,c_3298,c_3914,c_4270])).

cnf(c_6279,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6278])).

cnf(c_7332,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6618,c_48,c_49,c_50,c_51,c_55,c_56,c_3039,c_2975,c_2978,c_3275,c_3298,c_3914,c_4294,c_6279])).

cnf(c_7333,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7332])).

cnf(c_7340,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4526,c_7333])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_7344,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7340,c_2])).

cnf(c_4537,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4526,c_2978])).

cnf(c_4545,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4537,c_2])).

cnf(c_8128,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7344,c_4545])).

cnf(c_8129,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8128])).

cnf(c_8135,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4526,c_8129])).

cnf(c_8359,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5037,c_8135])).

cnf(c_8961,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8359,c_8135])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2946,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5206,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_2946])).

cnf(c_5340,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK3) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4545,c_5206])).

cnf(c_24,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2944,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | v1_funct_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_15846,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) != X0
    | v1_funct_2(sK3,X0,k1_xboole_0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5340,c_2944])).

cnf(c_15847,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) != X0
    | v1_funct_2(sK3,X0,k1_xboole_0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15846,c_2])).

cnf(c_15852,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) != X0
    | v1_funct_2(sK3,X0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15847,c_55,c_4545])).

cnf(c_15861,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_15852])).

cnf(c_16021,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15220,c_8961,c_15861])).

cnf(c_16069,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_16021,c_5029])).

cnf(c_19422,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(X0,X1,sK1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16069,c_2937])).

cnf(c_19457,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(X0,X1,sK1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19422,c_2])).

cnf(c_2939,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7666,plain,
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
    inference(superposition,[status(thm)],[c_2934,c_2939])).

cnf(c_57,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3271,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3272,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3271])).

cnf(c_3294,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3295,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3294])).

cnf(c_3440,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_3441,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3440])).

cnf(c_3415,plain,
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
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_3776,plain,
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
    inference(instantiation,[status(thm)],[c_3415])).

cnf(c_4371,plain,
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
    inference(instantiation,[status(thm)],[c_3776])).

cnf(c_4372,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4371])).

cnf(c_3435,plain,
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
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_3823,plain,
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
    inference(instantiation,[status(thm)],[c_3435])).

cnf(c_4395,plain,
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
    inference(instantiation,[status(thm)],[c_3823])).

cnf(c_4396,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4395])).

cnf(c_3706,plain,
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
    inference(instantiation,[status(thm)],[c_3395])).

cnf(c_4986,plain,
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
    inference(instantiation,[status(thm)],[c_3706])).

cnf(c_4987,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4986])).

cnf(c_8321,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7666,c_48,c_49,c_50,c_51,c_55,c_56,c_57,c_3039,c_3044,c_2975,c_2978,c_3272,c_3295,c_3441,c_4372,c_4396,c_4987])).

cnf(c_8322,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8321])).

cnf(c_8325,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8322,c_48,c_49,c_50,c_51,c_55,c_56,c_57,c_3039,c_2975,c_2978,c_3272,c_3295,c_3441,c_4396,c_4987])).

cnf(c_8332,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5029,c_8325])).

cnf(c_8343,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8332,c_2])).

cnf(c_5036,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5029,c_2934])).

cnf(c_5044,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5036,c_2])).

cnf(c_9863,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8343,c_5044])).

cnf(c_9864,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9863])).

cnf(c_9869,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5029,c_9864])).

cnf(c_16040,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16021,c_9869])).

cnf(c_5339,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK3) = k1_relat_1(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5044,c_5206])).

cnf(c_20252,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK3) = k1_relat_1(sK3)
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_5339,c_16021])).

cnf(c_20276,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | k1_relat_1(sK3) != X0
    | v1_funct_2(sK3,X0,k1_xboole_0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_20252,c_2944])).

cnf(c_20282,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | k1_relat_1(sK3) != X0
    | v1_funct_2(sK3,X0,k1_xboole_0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20276,c_2])).

cnf(c_16067,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16021,c_5044])).

cnf(c_20617,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | k1_relat_1(sK3) != X0
    | v1_funct_2(sK3,X0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20282,c_55,c_16067])).

cnf(c_20626,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_20617])).

cnf(c_20714,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19457,c_16040,c_20626])).

cnf(c_16051,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16021,c_7333])).

cnf(c_20719,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20714,c_16051])).

cnf(c_16076,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16021,c_2975])).

cnf(c_16075,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16021,c_2978])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20719,c_16076,c_16075])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.81/1.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/1.47  
% 7.81/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.81/1.47  
% 7.81/1.47  ------  iProver source info
% 7.81/1.47  
% 7.81/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.81/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.81/1.47  git: non_committed_changes: false
% 7.81/1.47  git: last_make_outside_of_git: false
% 7.81/1.47  
% 7.81/1.47  ------ 
% 7.81/1.47  
% 7.81/1.47  ------ Input Options
% 7.81/1.47  
% 7.81/1.47  --out_options                           all
% 7.81/1.47  --tptp_safe_out                         true
% 7.81/1.47  --problem_path                          ""
% 7.81/1.47  --include_path                          ""
% 7.81/1.47  --clausifier                            res/vclausify_rel
% 7.81/1.47  --clausifier_options                    --mode clausify
% 7.81/1.47  --stdin                                 false
% 7.81/1.47  --stats_out                             all
% 7.81/1.47  
% 7.81/1.47  ------ General Options
% 7.81/1.47  
% 7.81/1.47  --fof                                   false
% 7.81/1.47  --time_out_real                         305.
% 7.81/1.47  --time_out_virtual                      -1.
% 7.81/1.47  --symbol_type_check                     false
% 7.81/1.47  --clausify_out                          false
% 7.81/1.47  --sig_cnt_out                           false
% 7.81/1.47  --trig_cnt_out                          false
% 7.81/1.47  --trig_cnt_out_tolerance                1.
% 7.81/1.47  --trig_cnt_out_sk_spl                   false
% 7.81/1.47  --abstr_cl_out                          false
% 7.81/1.47  
% 7.81/1.47  ------ Global Options
% 7.81/1.47  
% 7.81/1.47  --schedule                              default
% 7.81/1.47  --add_important_lit                     false
% 7.81/1.47  --prop_solver_per_cl                    1000
% 7.81/1.47  --min_unsat_core                        false
% 7.81/1.47  --soft_assumptions                      false
% 7.81/1.47  --soft_lemma_size                       3
% 7.81/1.47  --prop_impl_unit_size                   0
% 7.81/1.47  --prop_impl_unit                        []
% 7.81/1.47  --share_sel_clauses                     true
% 7.81/1.47  --reset_solvers                         false
% 7.81/1.47  --bc_imp_inh                            [conj_cone]
% 7.81/1.47  --conj_cone_tolerance                   3.
% 7.81/1.47  --extra_neg_conj                        none
% 7.81/1.47  --large_theory_mode                     true
% 7.81/1.47  --prolific_symb_bound                   200
% 7.81/1.47  --lt_threshold                          2000
% 7.81/1.47  --clause_weak_htbl                      true
% 7.81/1.47  --gc_record_bc_elim                     false
% 7.81/1.47  
% 7.81/1.47  ------ Preprocessing Options
% 7.81/1.47  
% 7.81/1.47  --preprocessing_flag                    true
% 7.81/1.47  --time_out_prep_mult                    0.1
% 7.81/1.47  --splitting_mode                        input
% 7.81/1.47  --splitting_grd                         true
% 7.81/1.47  --splitting_cvd                         false
% 7.81/1.47  --splitting_cvd_svl                     false
% 7.81/1.47  --splitting_nvd                         32
% 7.81/1.47  --sub_typing                            true
% 7.81/1.47  --prep_gs_sim                           true
% 7.81/1.47  --prep_unflatten                        true
% 7.81/1.47  --prep_res_sim                          true
% 7.81/1.47  --prep_upred                            true
% 7.81/1.47  --prep_sem_filter                       exhaustive
% 7.81/1.47  --prep_sem_filter_out                   false
% 7.81/1.47  --pred_elim                             true
% 7.81/1.47  --res_sim_input                         true
% 7.81/1.47  --eq_ax_congr_red                       true
% 7.81/1.47  --pure_diseq_elim                       true
% 7.81/1.47  --brand_transform                       false
% 7.81/1.47  --non_eq_to_eq                          false
% 7.81/1.47  --prep_def_merge                        true
% 7.81/1.47  --prep_def_merge_prop_impl              false
% 7.81/1.47  --prep_def_merge_mbd                    true
% 7.81/1.47  --prep_def_merge_tr_red                 false
% 7.81/1.47  --prep_def_merge_tr_cl                  false
% 7.81/1.47  --smt_preprocessing                     true
% 7.81/1.47  --smt_ac_axioms                         fast
% 7.81/1.47  --preprocessed_out                      false
% 7.81/1.47  --preprocessed_stats                    false
% 7.81/1.47  
% 7.81/1.47  ------ Abstraction refinement Options
% 7.81/1.47  
% 7.81/1.47  --abstr_ref                             []
% 7.81/1.47  --abstr_ref_prep                        false
% 7.81/1.47  --abstr_ref_until_sat                   false
% 7.81/1.47  --abstr_ref_sig_restrict                funpre
% 7.81/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.47  --abstr_ref_under                       []
% 7.81/1.47  
% 7.81/1.47  ------ SAT Options
% 7.81/1.47  
% 7.81/1.47  --sat_mode                              false
% 7.81/1.47  --sat_fm_restart_options                ""
% 7.81/1.47  --sat_gr_def                            false
% 7.81/1.47  --sat_epr_types                         true
% 7.81/1.47  --sat_non_cyclic_types                  false
% 7.81/1.47  --sat_finite_models                     false
% 7.81/1.47  --sat_fm_lemmas                         false
% 7.81/1.47  --sat_fm_prep                           false
% 7.81/1.47  --sat_fm_uc_incr                        true
% 7.81/1.47  --sat_out_model                         small
% 7.81/1.47  --sat_out_clauses                       false
% 7.81/1.47  
% 7.81/1.47  ------ QBF Options
% 7.81/1.47  
% 7.81/1.47  --qbf_mode                              false
% 7.81/1.47  --qbf_elim_univ                         false
% 7.81/1.47  --qbf_dom_inst                          none
% 7.81/1.47  --qbf_dom_pre_inst                      false
% 7.81/1.47  --qbf_sk_in                             false
% 7.81/1.47  --qbf_pred_elim                         true
% 7.81/1.47  --qbf_split                             512
% 7.81/1.47  
% 7.81/1.47  ------ BMC1 Options
% 7.81/1.47  
% 7.81/1.47  --bmc1_incremental                      false
% 7.81/1.47  --bmc1_axioms                           reachable_all
% 7.81/1.47  --bmc1_min_bound                        0
% 7.81/1.47  --bmc1_max_bound                        -1
% 7.81/1.47  --bmc1_max_bound_default                -1
% 7.81/1.47  --bmc1_symbol_reachability              true
% 7.81/1.47  --bmc1_property_lemmas                  false
% 7.81/1.47  --bmc1_k_induction                      false
% 7.81/1.47  --bmc1_non_equiv_states                 false
% 7.81/1.47  --bmc1_deadlock                         false
% 7.81/1.47  --bmc1_ucm                              false
% 7.81/1.47  --bmc1_add_unsat_core                   none
% 7.81/1.47  --bmc1_unsat_core_children              false
% 7.81/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.47  --bmc1_out_stat                         full
% 7.81/1.47  --bmc1_ground_init                      false
% 7.81/1.47  --bmc1_pre_inst_next_state              false
% 7.81/1.47  --bmc1_pre_inst_state                   false
% 7.81/1.47  --bmc1_pre_inst_reach_state             false
% 7.81/1.47  --bmc1_out_unsat_core                   false
% 7.81/1.47  --bmc1_aig_witness_out                  false
% 7.81/1.47  --bmc1_verbose                          false
% 7.81/1.47  --bmc1_dump_clauses_tptp                false
% 7.81/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.47  --bmc1_dump_file                        -
% 7.81/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.47  --bmc1_ucm_extend_mode                  1
% 7.81/1.47  --bmc1_ucm_init_mode                    2
% 7.81/1.47  --bmc1_ucm_cone_mode                    none
% 7.81/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.47  --bmc1_ucm_relax_model                  4
% 7.81/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.47  --bmc1_ucm_layered_model                none
% 7.81/1.47  --bmc1_ucm_max_lemma_size               10
% 7.81/1.47  
% 7.81/1.47  ------ AIG Options
% 7.81/1.47  
% 7.81/1.47  --aig_mode                              false
% 7.81/1.47  
% 7.81/1.47  ------ Instantiation Options
% 7.81/1.47  
% 7.81/1.47  --instantiation_flag                    true
% 7.81/1.47  --inst_sos_flag                         false
% 7.81/1.47  --inst_sos_phase                        true
% 7.81/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.47  --inst_lit_sel_side                     num_symb
% 7.81/1.47  --inst_solver_per_active                1400
% 7.81/1.47  --inst_solver_calls_frac                1.
% 7.81/1.47  --inst_passive_queue_type               priority_queues
% 7.81/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.47  --inst_passive_queues_freq              [25;2]
% 7.81/1.47  --inst_dismatching                      true
% 7.81/1.47  --inst_eager_unprocessed_to_passive     true
% 7.81/1.47  --inst_prop_sim_given                   true
% 7.81/1.47  --inst_prop_sim_new                     false
% 7.81/1.47  --inst_subs_new                         false
% 7.81/1.47  --inst_eq_res_simp                      false
% 7.81/1.47  --inst_subs_given                       false
% 7.81/1.47  --inst_orphan_elimination               true
% 7.81/1.47  --inst_learning_loop_flag               true
% 7.81/1.47  --inst_learning_start                   3000
% 7.81/1.47  --inst_learning_factor                  2
% 7.81/1.47  --inst_start_prop_sim_after_learn       3
% 7.81/1.47  --inst_sel_renew                        solver
% 7.81/1.47  --inst_lit_activity_flag                true
% 7.81/1.47  --inst_restr_to_given                   false
% 7.81/1.47  --inst_activity_threshold               500
% 7.81/1.47  --inst_out_proof                        true
% 7.81/1.47  
% 7.81/1.47  ------ Resolution Options
% 7.81/1.47  
% 7.81/1.47  --resolution_flag                       true
% 7.81/1.47  --res_lit_sel                           adaptive
% 7.81/1.47  --res_lit_sel_side                      none
% 7.81/1.47  --res_ordering                          kbo
% 7.81/1.47  --res_to_prop_solver                    active
% 7.81/1.47  --res_prop_simpl_new                    false
% 7.81/1.47  --res_prop_simpl_given                  true
% 7.81/1.47  --res_passive_queue_type                priority_queues
% 7.81/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.47  --res_passive_queues_freq               [15;5]
% 7.81/1.47  --res_forward_subs                      full
% 7.81/1.47  --res_backward_subs                     full
% 7.81/1.47  --res_forward_subs_resolution           true
% 7.81/1.47  --res_backward_subs_resolution          true
% 7.81/1.47  --res_orphan_elimination                true
% 7.81/1.47  --res_time_limit                        2.
% 7.81/1.47  --res_out_proof                         true
% 7.81/1.47  
% 7.81/1.47  ------ Superposition Options
% 7.81/1.47  
% 7.81/1.47  --superposition_flag                    true
% 7.81/1.47  --sup_passive_queue_type                priority_queues
% 7.81/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.47  --demod_completeness_check              fast
% 7.81/1.47  --demod_use_ground                      true
% 7.81/1.47  --sup_to_prop_solver                    passive
% 7.81/1.47  --sup_prop_simpl_new                    true
% 7.81/1.47  --sup_prop_simpl_given                  true
% 7.81/1.47  --sup_fun_splitting                     false
% 7.81/1.47  --sup_smt_interval                      50000
% 7.81/1.47  
% 7.81/1.47  ------ Superposition Simplification Setup
% 7.81/1.47  
% 7.81/1.47  --sup_indices_passive                   []
% 7.81/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.47  --sup_full_bw                           [BwDemod]
% 7.81/1.47  --sup_immed_triv                        [TrivRules]
% 7.81/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.47  --sup_immed_bw_main                     []
% 7.81/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.47  
% 7.81/1.47  ------ Combination Options
% 7.81/1.47  
% 7.81/1.47  --comb_res_mult                         3
% 7.81/1.47  --comb_sup_mult                         2
% 7.81/1.47  --comb_inst_mult                        10
% 7.81/1.47  
% 7.81/1.47  ------ Debug Options
% 7.81/1.47  
% 7.81/1.47  --dbg_backtrace                         false
% 7.81/1.47  --dbg_dump_prop_clauses                 false
% 7.81/1.47  --dbg_dump_prop_clauses_file            -
% 7.81/1.47  --dbg_out_stat                          false
% 7.81/1.47  ------ Parsing...
% 7.81/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.81/1.47  
% 7.81/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.81/1.47  
% 7.81/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.81/1.47  
% 7.81/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.47  ------ Proving...
% 7.81/1.47  ------ Problem Properties 
% 7.81/1.47  
% 7.81/1.47  
% 7.81/1.47  clauses                                 37
% 7.81/1.47  conjectures                             13
% 7.81/1.47  EPR                                     11
% 7.81/1.47  Horn                                    31
% 7.81/1.47  unary                                   15
% 7.81/1.47  binary                                  5
% 7.81/1.47  lits                                    119
% 7.81/1.47  lits eq                                 13
% 7.81/1.47  fd_pure                                 0
% 7.81/1.47  fd_pseudo                               0
% 7.81/1.47  fd_cond                                 1
% 7.81/1.47  fd_pseudo_cond                          3
% 7.81/1.47  AC symbols                              0
% 7.81/1.47  
% 7.81/1.47  ------ Schedule dynamic 5 is on 
% 7.81/1.47  
% 7.81/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.81/1.47  
% 7.81/1.47  
% 7.81/1.47  ------ 
% 7.81/1.47  Current options:
% 7.81/1.47  ------ 
% 7.81/1.47  
% 7.81/1.47  ------ Input Options
% 7.81/1.47  
% 7.81/1.47  --out_options                           all
% 7.81/1.47  --tptp_safe_out                         true
% 7.81/1.47  --problem_path                          ""
% 7.81/1.47  --include_path                          ""
% 7.81/1.47  --clausifier                            res/vclausify_rel
% 7.81/1.47  --clausifier_options                    --mode clausify
% 7.81/1.47  --stdin                                 false
% 7.81/1.47  --stats_out                             all
% 7.81/1.48  
% 7.81/1.48  ------ General Options
% 7.81/1.48  
% 7.81/1.48  --fof                                   false
% 7.81/1.48  --time_out_real                         305.
% 7.81/1.48  --time_out_virtual                      -1.
% 7.81/1.48  --symbol_type_check                     false
% 7.81/1.48  --clausify_out                          false
% 7.81/1.48  --sig_cnt_out                           false
% 7.81/1.48  --trig_cnt_out                          false
% 7.81/1.48  --trig_cnt_out_tolerance                1.
% 7.81/1.48  --trig_cnt_out_sk_spl                   false
% 7.81/1.48  --abstr_cl_out                          false
% 7.81/1.48  
% 7.81/1.48  ------ Global Options
% 7.81/1.48  
% 7.81/1.48  --schedule                              default
% 7.81/1.48  --add_important_lit                     false
% 7.81/1.48  --prop_solver_per_cl                    1000
% 7.81/1.48  --min_unsat_core                        false
% 7.81/1.48  --soft_assumptions                      false
% 7.81/1.48  --soft_lemma_size                       3
% 7.81/1.48  --prop_impl_unit_size                   0
% 7.81/1.48  --prop_impl_unit                        []
% 7.81/1.48  --share_sel_clauses                     true
% 7.81/1.48  --reset_solvers                         false
% 7.81/1.48  --bc_imp_inh                            [conj_cone]
% 7.81/1.48  --conj_cone_tolerance                   3.
% 7.81/1.48  --extra_neg_conj                        none
% 7.81/1.48  --large_theory_mode                     true
% 7.81/1.48  --prolific_symb_bound                   200
% 7.81/1.48  --lt_threshold                          2000
% 7.81/1.48  --clause_weak_htbl                      true
% 7.81/1.48  --gc_record_bc_elim                     false
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing Options
% 7.81/1.48  
% 7.81/1.48  --preprocessing_flag                    true
% 7.81/1.48  --time_out_prep_mult                    0.1
% 7.81/1.48  --splitting_mode                        input
% 7.81/1.48  --splitting_grd                         true
% 7.81/1.48  --splitting_cvd                         false
% 7.81/1.48  --splitting_cvd_svl                     false
% 7.81/1.48  --splitting_nvd                         32
% 7.81/1.48  --sub_typing                            true
% 7.81/1.48  --prep_gs_sim                           true
% 7.81/1.48  --prep_unflatten                        true
% 7.81/1.48  --prep_res_sim                          true
% 7.81/1.48  --prep_upred                            true
% 7.81/1.48  --prep_sem_filter                       exhaustive
% 7.81/1.48  --prep_sem_filter_out                   false
% 7.81/1.48  --pred_elim                             true
% 7.81/1.48  --res_sim_input                         true
% 7.81/1.48  --eq_ax_congr_red                       true
% 7.81/1.48  --pure_diseq_elim                       true
% 7.81/1.48  --brand_transform                       false
% 7.81/1.48  --non_eq_to_eq                          false
% 7.81/1.48  --prep_def_merge                        true
% 7.81/1.48  --prep_def_merge_prop_impl              false
% 7.81/1.48  --prep_def_merge_mbd                    true
% 7.81/1.48  --prep_def_merge_tr_red                 false
% 7.81/1.48  --prep_def_merge_tr_cl                  false
% 7.81/1.48  --smt_preprocessing                     true
% 7.81/1.48  --smt_ac_axioms                         fast
% 7.81/1.48  --preprocessed_out                      false
% 7.81/1.48  --preprocessed_stats                    false
% 7.81/1.48  
% 7.81/1.48  ------ Abstraction refinement Options
% 7.81/1.48  
% 7.81/1.48  --abstr_ref                             []
% 7.81/1.48  --abstr_ref_prep                        false
% 7.81/1.48  --abstr_ref_until_sat                   false
% 7.81/1.48  --abstr_ref_sig_restrict                funpre
% 7.81/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.48  --abstr_ref_under                       []
% 7.81/1.48  
% 7.81/1.48  ------ SAT Options
% 7.81/1.48  
% 7.81/1.48  --sat_mode                              false
% 7.81/1.48  --sat_fm_restart_options                ""
% 7.81/1.48  --sat_gr_def                            false
% 7.81/1.48  --sat_epr_types                         true
% 7.81/1.48  --sat_non_cyclic_types                  false
% 7.81/1.48  --sat_finite_models                     false
% 7.81/1.48  --sat_fm_lemmas                         false
% 7.81/1.48  --sat_fm_prep                           false
% 7.81/1.48  --sat_fm_uc_incr                        true
% 7.81/1.48  --sat_out_model                         small
% 7.81/1.48  --sat_out_clauses                       false
% 7.81/1.48  
% 7.81/1.48  ------ QBF Options
% 7.81/1.48  
% 7.81/1.48  --qbf_mode                              false
% 7.81/1.48  --qbf_elim_univ                         false
% 7.81/1.48  --qbf_dom_inst                          none
% 7.81/1.48  --qbf_dom_pre_inst                      false
% 7.81/1.48  --qbf_sk_in                             false
% 7.81/1.48  --qbf_pred_elim                         true
% 7.81/1.48  --qbf_split                             512
% 7.81/1.48  
% 7.81/1.48  ------ BMC1 Options
% 7.81/1.48  
% 7.81/1.48  --bmc1_incremental                      false
% 7.81/1.48  --bmc1_axioms                           reachable_all
% 7.81/1.48  --bmc1_min_bound                        0
% 7.81/1.48  --bmc1_max_bound                        -1
% 7.81/1.48  --bmc1_max_bound_default                -1
% 7.81/1.48  --bmc1_symbol_reachability              true
% 7.81/1.48  --bmc1_property_lemmas                  false
% 7.81/1.48  --bmc1_k_induction                      false
% 7.81/1.48  --bmc1_non_equiv_states                 false
% 7.81/1.48  --bmc1_deadlock                         false
% 7.81/1.48  --bmc1_ucm                              false
% 7.81/1.48  --bmc1_add_unsat_core                   none
% 7.81/1.48  --bmc1_unsat_core_children              false
% 7.81/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.48  --bmc1_out_stat                         full
% 7.81/1.48  --bmc1_ground_init                      false
% 7.81/1.48  --bmc1_pre_inst_next_state              false
% 7.81/1.48  --bmc1_pre_inst_state                   false
% 7.81/1.48  --bmc1_pre_inst_reach_state             false
% 7.81/1.48  --bmc1_out_unsat_core                   false
% 7.81/1.48  --bmc1_aig_witness_out                  false
% 7.81/1.48  --bmc1_verbose                          false
% 7.81/1.48  --bmc1_dump_clauses_tptp                false
% 7.81/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.48  --bmc1_dump_file                        -
% 7.81/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.48  --bmc1_ucm_extend_mode                  1
% 7.81/1.48  --bmc1_ucm_init_mode                    2
% 7.81/1.48  --bmc1_ucm_cone_mode                    none
% 7.81/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.48  --bmc1_ucm_relax_model                  4
% 7.81/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.48  --bmc1_ucm_layered_model                none
% 7.81/1.48  --bmc1_ucm_max_lemma_size               10
% 7.81/1.48  
% 7.81/1.48  ------ AIG Options
% 7.81/1.48  
% 7.81/1.48  --aig_mode                              false
% 7.81/1.48  
% 7.81/1.48  ------ Instantiation Options
% 7.81/1.48  
% 7.81/1.48  --instantiation_flag                    true
% 7.81/1.48  --inst_sos_flag                         false
% 7.81/1.48  --inst_sos_phase                        true
% 7.81/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.48  --inst_lit_sel_side                     none
% 7.81/1.48  --inst_solver_per_active                1400
% 7.81/1.48  --inst_solver_calls_frac                1.
% 7.81/1.48  --inst_passive_queue_type               priority_queues
% 7.81/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.48  --inst_passive_queues_freq              [25;2]
% 7.81/1.48  --inst_dismatching                      true
% 7.81/1.48  --inst_eager_unprocessed_to_passive     true
% 7.81/1.48  --inst_prop_sim_given                   true
% 7.81/1.48  --inst_prop_sim_new                     false
% 7.81/1.48  --inst_subs_new                         false
% 7.81/1.48  --inst_eq_res_simp                      false
% 7.81/1.48  --inst_subs_given                       false
% 7.81/1.48  --inst_orphan_elimination               true
% 7.81/1.48  --inst_learning_loop_flag               true
% 7.81/1.48  --inst_learning_start                   3000
% 7.81/1.48  --inst_learning_factor                  2
% 7.81/1.48  --inst_start_prop_sim_after_learn       3
% 7.81/1.48  --inst_sel_renew                        solver
% 7.81/1.48  --inst_lit_activity_flag                true
% 7.81/1.48  --inst_restr_to_given                   false
% 7.81/1.48  --inst_activity_threshold               500
% 7.81/1.48  --inst_out_proof                        true
% 7.81/1.48  
% 7.81/1.48  ------ Resolution Options
% 7.81/1.48  
% 7.81/1.48  --resolution_flag                       false
% 7.81/1.48  --res_lit_sel                           adaptive
% 7.81/1.48  --res_lit_sel_side                      none
% 7.81/1.48  --res_ordering                          kbo
% 7.81/1.48  --res_to_prop_solver                    active
% 7.81/1.48  --res_prop_simpl_new                    false
% 7.81/1.48  --res_prop_simpl_given                  true
% 7.81/1.48  --res_passive_queue_type                priority_queues
% 7.81/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.48  --res_passive_queues_freq               [15;5]
% 7.81/1.48  --res_forward_subs                      full
% 7.81/1.48  --res_backward_subs                     full
% 7.81/1.48  --res_forward_subs_resolution           true
% 7.81/1.48  --res_backward_subs_resolution          true
% 7.81/1.48  --res_orphan_elimination                true
% 7.81/1.48  --res_time_limit                        2.
% 7.81/1.48  --res_out_proof                         true
% 7.81/1.48  
% 7.81/1.48  ------ Superposition Options
% 7.81/1.48  
% 7.81/1.48  --superposition_flag                    true
% 7.81/1.48  --sup_passive_queue_type                priority_queues
% 7.81/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.48  --demod_completeness_check              fast
% 7.81/1.48  --demod_use_ground                      true
% 7.81/1.48  --sup_to_prop_solver                    passive
% 7.81/1.48  --sup_prop_simpl_new                    true
% 7.81/1.48  --sup_prop_simpl_given                  true
% 7.81/1.48  --sup_fun_splitting                     false
% 7.81/1.48  --sup_smt_interval                      50000
% 7.81/1.48  
% 7.81/1.48  ------ Superposition Simplification Setup
% 7.81/1.48  
% 7.81/1.48  --sup_indices_passive                   []
% 7.81/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.48  --sup_full_bw                           [BwDemod]
% 7.81/1.48  --sup_immed_triv                        [TrivRules]
% 7.81/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.48  --sup_immed_bw_main                     []
% 7.81/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.48  
% 7.81/1.48  ------ Combination Options
% 7.81/1.48  
% 7.81/1.48  --comb_res_mult                         3
% 7.81/1.48  --comb_sup_mult                         2
% 7.81/1.48  --comb_inst_mult                        10
% 7.81/1.48  
% 7.81/1.48  ------ Debug Options
% 7.81/1.48  
% 7.81/1.48  --dbg_backtrace                         false
% 7.81/1.48  --dbg_dump_prop_clauses                 false
% 7.81/1.48  --dbg_dump_prop_clauses_file            -
% 7.81/1.48  --dbg_out_stat                          false
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  % SZS status Theorem for theBenchmark.p
% 7.81/1.48  
% 7.81/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.81/1.48  
% 7.81/1.48  fof(f22,conjecture,(
% 7.81/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f23,negated_conjecture,(
% 7.81/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.81/1.48    inference(negated_conjecture,[],[f22])).
% 7.81/1.48  
% 7.81/1.48  fof(f54,plain,(
% 7.81/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.81/1.48    inference(ennf_transformation,[],[f23])).
% 7.81/1.48  
% 7.81/1.48  fof(f55,plain,(
% 7.81/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.81/1.48    inference(flattening,[],[f54])).
% 7.81/1.48  
% 7.81/1.48  fof(f62,plain,(
% 7.81/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.81/1.48    inference(nnf_transformation,[],[f55])).
% 7.81/1.48  
% 7.81/1.48  fof(f63,plain,(
% 7.81/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.81/1.48    inference(flattening,[],[f62])).
% 7.81/1.48  
% 7.81/1.48  fof(f67,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK3 = X2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK3))) )),
% 7.81/1.48    introduced(choice_axiom,[])).
% 7.81/1.48  
% 7.81/1.48  fof(f66,plain,(
% 7.81/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 7.81/1.48    introduced(choice_axiom,[])).
% 7.81/1.48  
% 7.81/1.48  fof(f65,plain,(
% 7.81/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,X0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,X0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 7.81/1.48    introduced(choice_axiom,[])).
% 7.81/1.48  
% 7.81/1.48  fof(f64,plain,(
% 7.81/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.81/1.48    introduced(choice_axiom,[])).
% 7.81/1.48  
% 7.81/1.48  fof(f68,plain,(
% 7.81/1.48    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.81/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f63,f67,f66,f65,f64])).
% 7.81/1.48  
% 7.81/1.48  fof(f110,plain,(
% 7.81/1.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 7.81/1.48    inference(cnf_transformation,[],[f68])).
% 7.81/1.48  
% 7.81/1.48  fof(f114,plain,(
% 7.81/1.48    sK2 = sK3),
% 7.81/1.48    inference(cnf_transformation,[],[f68])).
% 7.81/1.48  
% 7.81/1.48  fof(f16,axiom,(
% 7.81/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f44,plain,(
% 7.81/1.48    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.81/1.48    inference(ennf_transformation,[],[f16])).
% 7.81/1.48  
% 7.81/1.48  fof(f45,plain,(
% 7.81/1.48    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.81/1.48    inference(flattening,[],[f44])).
% 7.81/1.48  
% 7.81/1.48  fof(f95,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f45])).
% 7.81/1.48  
% 7.81/1.48  fof(f9,axiom,(
% 7.81/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f26,plain,(
% 7.81/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.81/1.48    inference(pure_predicate_removal,[],[f9])).
% 7.81/1.48  
% 7.81/1.48  fof(f33,plain,(
% 7.81/1.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.81/1.48    inference(ennf_transformation,[],[f26])).
% 7.81/1.48  
% 7.81/1.48  fof(f82,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.48    inference(cnf_transformation,[],[f33])).
% 7.81/1.48  
% 7.81/1.48  fof(f14,axiom,(
% 7.81/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f40,plain,(
% 7.81/1.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.81/1.48    inference(ennf_transformation,[],[f14])).
% 7.81/1.48  
% 7.81/1.48  fof(f41,plain,(
% 7.81/1.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.81/1.48    inference(flattening,[],[f40])).
% 7.81/1.48  
% 7.81/1.48  fof(f59,plain,(
% 7.81/1.48    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.81/1.48    inference(nnf_transformation,[],[f41])).
% 7.81/1.48  
% 7.81/1.48  fof(f90,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f59])).
% 7.81/1.48  
% 7.81/1.48  fof(f8,axiom,(
% 7.81/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f32,plain,(
% 7.81/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.81/1.48    inference(ennf_transformation,[],[f8])).
% 7.81/1.48  
% 7.81/1.48  fof(f81,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.48    inference(cnf_transformation,[],[f32])).
% 7.81/1.48  
% 7.81/1.48  fof(f1,axiom,(
% 7.81/1.48    v1_xboole_0(k1_xboole_0)),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f69,plain,(
% 7.81/1.48    v1_xboole_0(k1_xboole_0)),
% 7.81/1.48    inference(cnf_transformation,[],[f1])).
% 7.81/1.48  
% 7.81/1.48  fof(f12,axiom,(
% 7.81/1.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f36,plain,(
% 7.81/1.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.81/1.48    inference(ennf_transformation,[],[f12])).
% 7.81/1.48  
% 7.81/1.48  fof(f37,plain,(
% 7.81/1.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.81/1.48    inference(flattening,[],[f36])).
% 7.81/1.48  
% 7.81/1.48  fof(f86,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f37])).
% 7.81/1.48  
% 7.81/1.48  fof(f111,plain,(
% 7.81/1.48    v1_funct_1(sK3)),
% 7.81/1.48    inference(cnf_transformation,[],[f68])).
% 7.81/1.48  
% 7.81/1.48  fof(f109,plain,(
% 7.81/1.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 7.81/1.48    inference(cnf_transformation,[],[f68])).
% 7.81/1.48  
% 7.81/1.48  fof(f2,axiom,(
% 7.81/1.48    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f27,plain,(
% 7.81/1.48    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 7.81/1.48    inference(ennf_transformation,[],[f2])).
% 7.81/1.48  
% 7.81/1.48  fof(f70,plain,(
% 7.81/1.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f27])).
% 7.81/1.48  
% 7.81/1.48  fof(f18,axiom,(
% 7.81/1.48    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f47,plain,(
% 7.81/1.48    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.81/1.48    inference(ennf_transformation,[],[f18])).
% 7.81/1.48  
% 7.81/1.48  fof(f98,plain,(
% 7.81/1.48    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f47])).
% 7.81/1.48  
% 7.81/1.48  fof(f4,axiom,(
% 7.81/1.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f28,plain,(
% 7.81/1.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.81/1.48    inference(ennf_transformation,[],[f4])).
% 7.81/1.48  
% 7.81/1.48  fof(f58,plain,(
% 7.81/1.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.81/1.48    inference(nnf_transformation,[],[f28])).
% 7.81/1.48  
% 7.81/1.48  fof(f74,plain,(
% 7.81/1.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f58])).
% 7.81/1.48  
% 7.81/1.48  fof(f7,axiom,(
% 7.81/1.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f30,plain,(
% 7.81/1.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.81/1.48    inference(ennf_transformation,[],[f7])).
% 7.81/1.48  
% 7.81/1.48  fof(f31,plain,(
% 7.81/1.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.81/1.48    inference(flattening,[],[f30])).
% 7.81/1.48  
% 7.81/1.48  fof(f80,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f31])).
% 7.81/1.48  
% 7.81/1.48  fof(f113,plain,(
% 7.81/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 7.81/1.48    inference(cnf_transformation,[],[f68])).
% 7.81/1.48  
% 7.81/1.48  fof(f112,plain,(
% 7.81/1.48    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 7.81/1.48    inference(cnf_transformation,[],[f68])).
% 7.81/1.48  
% 7.81/1.48  fof(f21,axiom,(
% 7.81/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f52,plain,(
% 7.81/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.81/1.48    inference(ennf_transformation,[],[f21])).
% 7.81/1.48  
% 7.81/1.48  fof(f53,plain,(
% 7.81/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.81/1.48    inference(flattening,[],[f52])).
% 7.81/1.48  
% 7.81/1.48  fof(f61,plain,(
% 7.81/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.81/1.48    inference(nnf_transformation,[],[f53])).
% 7.81/1.48  
% 7.81/1.48  fof(f103,plain,(
% 7.81/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f61])).
% 7.81/1.48  
% 7.81/1.48  fof(f123,plain,(
% 7.81/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.81/1.48    inference(equality_resolution,[],[f103])).
% 7.81/1.48  
% 7.81/1.48  fof(f104,plain,(
% 7.81/1.48    v2_pre_topc(sK0)),
% 7.81/1.48    inference(cnf_transformation,[],[f68])).
% 7.81/1.48  
% 7.81/1.48  fof(f105,plain,(
% 7.81/1.48    l1_pre_topc(sK0)),
% 7.81/1.48    inference(cnf_transformation,[],[f68])).
% 7.81/1.48  
% 7.81/1.48  fof(f106,plain,(
% 7.81/1.48    v2_pre_topc(sK1)),
% 7.81/1.48    inference(cnf_transformation,[],[f68])).
% 7.81/1.48  
% 7.81/1.48  fof(f107,plain,(
% 7.81/1.48    l1_pre_topc(sK1)),
% 7.81/1.48    inference(cnf_transformation,[],[f68])).
% 7.81/1.48  
% 7.81/1.48  fof(f115,plain,(
% 7.81/1.48    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 7.81/1.48    inference(cnf_transformation,[],[f68])).
% 7.81/1.48  
% 7.81/1.48  fof(f19,axiom,(
% 7.81/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f24,plain,(
% 7.81/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 7.81/1.48    inference(pure_predicate_removal,[],[f19])).
% 7.81/1.48  
% 7.81/1.48  fof(f48,plain,(
% 7.81/1.48    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.81/1.48    inference(ennf_transformation,[],[f24])).
% 7.81/1.48  
% 7.81/1.48  fof(f49,plain,(
% 7.81/1.48    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.81/1.48    inference(flattening,[],[f48])).
% 7.81/1.48  
% 7.81/1.48  fof(f99,plain,(
% 7.81/1.48    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f49])).
% 7.81/1.48  
% 7.81/1.48  fof(f17,axiom,(
% 7.81/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f25,plain,(
% 7.81/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 7.81/1.48    inference(pure_predicate_removal,[],[f17])).
% 7.81/1.48  
% 7.81/1.48  fof(f46,plain,(
% 7.81/1.48    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.81/1.48    inference(ennf_transformation,[],[f25])).
% 7.81/1.48  
% 7.81/1.48  fof(f97,plain,(
% 7.81/1.48    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.81/1.48    inference(cnf_transformation,[],[f46])).
% 7.81/1.48  
% 7.81/1.48  fof(f20,axiom,(
% 7.81/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f50,plain,(
% 7.81/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.81/1.48    inference(ennf_transformation,[],[f20])).
% 7.81/1.48  
% 7.81/1.48  fof(f51,plain,(
% 7.81/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.81/1.48    inference(flattening,[],[f50])).
% 7.81/1.48  
% 7.81/1.48  fof(f60,plain,(
% 7.81/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.81/1.48    inference(nnf_transformation,[],[f51])).
% 7.81/1.48  
% 7.81/1.48  fof(f100,plain,(
% 7.81/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f60])).
% 7.81/1.48  
% 7.81/1.48  fof(f122,plain,(
% 7.81/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.81/1.48    inference(equality_resolution,[],[f100])).
% 7.81/1.48  
% 7.81/1.48  fof(f102,plain,(
% 7.81/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f61])).
% 7.81/1.48  
% 7.81/1.48  fof(f124,plain,(
% 7.81/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.81/1.48    inference(equality_resolution,[],[f102])).
% 7.81/1.48  
% 7.81/1.48  fof(f116,plain,(
% 7.81/1.48    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 7.81/1.48    inference(cnf_transformation,[],[f68])).
% 7.81/1.48  
% 7.81/1.48  fof(f101,plain,(
% 7.81/1.48    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f60])).
% 7.81/1.48  
% 7.81/1.48  fof(f121,plain,(
% 7.81/1.48    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.81/1.48    inference(equality_resolution,[],[f101])).
% 7.81/1.48  
% 7.81/1.48  fof(f3,axiom,(
% 7.81/1.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f56,plain,(
% 7.81/1.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.81/1.48    inference(nnf_transformation,[],[f3])).
% 7.81/1.48  
% 7.81/1.48  fof(f57,plain,(
% 7.81/1.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.81/1.48    inference(flattening,[],[f56])).
% 7.81/1.48  
% 7.81/1.48  fof(f73,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.81/1.48    inference(cnf_transformation,[],[f57])).
% 7.81/1.48  
% 7.81/1.48  fof(f117,plain,(
% 7.81/1.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.81/1.48    inference(equality_resolution,[],[f73])).
% 7.81/1.48  
% 7.81/1.48  fof(f11,axiom,(
% 7.81/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f35,plain,(
% 7.81/1.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.81/1.48    inference(ennf_transformation,[],[f11])).
% 7.81/1.48  
% 7.81/1.48  fof(f84,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.48    inference(cnf_transformation,[],[f35])).
% 7.81/1.48  
% 7.81/1.48  fof(f15,axiom,(
% 7.81/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f42,plain,(
% 7.81/1.48    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.81/1.48    inference(ennf_transformation,[],[f15])).
% 7.81/1.48  
% 7.81/1.48  fof(f43,plain,(
% 7.81/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.81/1.48    inference(flattening,[],[f42])).
% 7.81/1.48  
% 7.81/1.48  fof(f93,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f43])).
% 7.81/1.48  
% 7.81/1.48  cnf(c_41,negated_conjecture,
% 7.81/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 7.81/1.48      inference(cnf_transformation,[],[f110]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2931,plain,
% 7.81/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_37,negated_conjecture,
% 7.81/1.48      ( sK2 = sK3 ),
% 7.81/1.48      inference(cnf_transformation,[],[f114]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2978,plain,
% 7.81/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.81/1.48      inference(light_normalisation,[status(thm)],[c_2931,c_37]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_27,plain,
% 7.81/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.48      | v1_partfun1(X0,X1)
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.48      | ~ v1_funct_1(X0)
% 7.81/1.48      | k1_xboole_0 = X2 ),
% 7.81/1.48      inference(cnf_transformation,[],[f95]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_13,plain,
% 7.81/1.48      ( v4_relat_1(X0,X1)
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.81/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_22,plain,
% 7.81/1.48      ( ~ v1_partfun1(X0,X1)
% 7.81/1.48      | ~ v4_relat_1(X0,X1)
% 7.81/1.48      | ~ v1_relat_1(X0)
% 7.81/1.48      | k1_relat_1(X0) = X1 ),
% 7.81/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_564,plain,
% 7.81/1.48      ( ~ v1_partfun1(X0,X1)
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.48      | ~ v1_relat_1(X0)
% 7.81/1.48      | k1_relat_1(X0) = X1 ),
% 7.81/1.48      inference(resolution,[status(thm)],[c_13,c_22]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_12,plain,
% 7.81/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.48      | v1_relat_1(X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_568,plain,
% 7.81/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.48      | ~ v1_partfun1(X0,X1)
% 7.81/1.48      | k1_relat_1(X0) = X1 ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_564,c_22,c_13,c_12]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_569,plain,
% 7.81/1.48      ( ~ v1_partfun1(X0,X1)
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.48      | k1_relat_1(X0) = X1 ),
% 7.81/1.48      inference(renaming,[status(thm)],[c_568]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_629,plain,
% 7.81/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.81/1.48      | ~ v1_funct_1(X0)
% 7.81/1.48      | k1_relat_1(X0) = X1
% 7.81/1.48      | k1_xboole_0 = X2 ),
% 7.81/1.48      inference(resolution,[status(thm)],[c_27,c_569]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_633,plain,
% 7.81/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.48      | ~ v1_funct_2(X0,X1,X2)
% 7.81/1.48      | ~ v1_funct_1(X0)
% 7.81/1.48      | k1_relat_1(X0) = X1
% 7.81/1.48      | k1_xboole_0 = X2 ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_629,c_27,c_12,c_564]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_634,plain,
% 7.81/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.48      | ~ v1_funct_1(X0)
% 7.81/1.48      | k1_relat_1(X0) = X1
% 7.81/1.48      | k1_xboole_0 = X2 ),
% 7.81/1.48      inference(renaming,[status(thm)],[c_633]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2923,plain,
% 7.81/1.48      ( k1_relat_1(X0) = X1
% 7.81/1.48      | k1_xboole_0 = X2
% 7.81/1.48      | v1_funct_2(X0,X1,X2) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.81/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4321,plain,
% 7.81/1.48      ( u1_struct_0(sK1) = k1_xboole_0
% 7.81/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_2978,c_2923]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_0,plain,
% 7.81/1.48      ( v1_xboole_0(k1_xboole_0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_16,plain,
% 7.81/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.48      | v1_partfun1(X0,X1)
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.48      | ~ v1_funct_1(X0)
% 7.81/1.48      | v1_xboole_0(X2) ),
% 7.81/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_653,plain,
% 7.81/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.81/1.48      | ~ v1_funct_1(X0)
% 7.81/1.48      | v1_xboole_0(X2)
% 7.81/1.48      | k1_relat_1(X0) = X1 ),
% 7.81/1.48      inference(resolution,[status(thm)],[c_16,c_569]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_655,plain,
% 7.81/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.48      | ~ v1_funct_2(X0,X1,X2)
% 7.81/1.48      | ~ v1_funct_1(X0)
% 7.81/1.48      | v1_xboole_0(X2)
% 7.81/1.48      | k1_relat_1(X0) = X1 ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_653,c_22,c_16,c_13,c_12]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_656,plain,
% 7.81/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.48      | ~ v1_funct_1(X0)
% 7.81/1.48      | v1_xboole_0(X2)
% 7.81/1.48      | k1_relat_1(X0) = X1 ),
% 7.81/1.48      inference(renaming,[status(thm)],[c_655]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2922,plain,
% 7.81/1.48      ( k1_relat_1(X0) = X1
% 7.81/1.48      | v1_funct_2(X0,X1,X2) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.81/1.48      | v1_funct_1(X0) != iProver_top
% 7.81/1.48      | v1_xboole_0(X2) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3426,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top
% 7.81/1.48      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_2978,c_2922]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_40,negated_conjecture,
% 7.81/1.48      ( v1_funct_1(sK3) ),
% 7.81/1.48      inference(cnf_transformation,[],[f111]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_55,plain,
% 7.81/1.48      ( v1_funct_1(sK3) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_42,negated_conjecture,
% 7.81/1.48      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 7.81/1.48      inference(cnf_transformation,[],[f109]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2930,plain,
% 7.81/1.48      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2975,plain,
% 7.81/1.48      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.81/1.48      inference(light_normalisation,[status(thm)],[c_2930,c_37]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3999,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_3426,c_55,c_2975]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_1,plain,
% 7.81/1.48      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 7.81/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2952,plain,
% 7.81/1.48      ( X0 = X1
% 7.81/1.48      | v1_xboole_0(X0) != iProver_top
% 7.81/1.48      | v1_xboole_0(X1) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4447,plain,
% 7.81/1.48      ( u1_struct_0(sK1) = X0
% 7.81/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | v1_xboole_0(X0) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_3999,c_2952]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4466,plain,
% 7.81/1.48      ( ~ v1_xboole_0(X0)
% 7.81/1.48      | u1_struct_0(sK1) = X0
% 7.81/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.81/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_4447]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4468,plain,
% 7.81/1.48      ( ~ v1_xboole_0(k1_xboole_0)
% 7.81/1.48      | u1_struct_0(sK1) = k1_xboole_0
% 7.81/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_4466]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4526,plain,
% 7.81/1.48      ( u1_struct_0(sK1) = k1_xboole_0
% 7.81/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_4321,c_0,c_4468]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_29,plain,
% 7.81/1.48      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.81/1.48      | ~ l1_pre_topc(X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f98]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2942,plain,
% 7.81/1.48      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 7.81/1.48      | l1_pre_topc(X0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_8,plain,
% 7.81/1.48      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 7.81/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_11,plain,
% 7.81/1.48      ( ~ r2_hidden(X0,X1)
% 7.81/1.48      | m1_subset_1(X0,X2)
% 7.81/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 7.81/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_608,plain,
% 7.81/1.48      ( ~ m1_subset_1(X0,X1)
% 7.81/1.48      | m1_subset_1(X0,X2)
% 7.81/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 7.81/1.48      | v1_xboole_0(X1) ),
% 7.81/1.48      inference(resolution,[status(thm)],[c_8,c_11]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2924,plain,
% 7.81/1.48      ( m1_subset_1(X0,X1) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,X2) = iProver_top
% 7.81/1.48      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 7.81/1.48      | v1_xboole_0(X1) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5116,plain,
% 7.81/1.48      ( m1_subset_1(X0,u1_pre_topc(X1)) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.81/1.48      | l1_pre_topc(X1) != iProver_top
% 7.81/1.48      | v1_xboole_0(u1_pre_topc(X1)) = iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_2942,c_2924]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_15220,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | m1_subset_1(X0,u1_pre_topc(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.81/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.81/1.48      | v1_xboole_0(u1_pre_topc(sK1)) = iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_4526,c_5116]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_38,negated_conjecture,
% 7.81/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
% 7.81/1.48      inference(cnf_transformation,[],[f113]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2934,plain,
% 7.81/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4320,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 7.81/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_2934,c_2923]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_39,negated_conjecture,
% 7.81/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
% 7.81/1.48      inference(cnf_transformation,[],[f112]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4359,plain,
% 7.81/1.48      ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.81/1.48      | ~ v1_funct_1(sK3)
% 7.81/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 7.81/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.81/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_4320]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5029,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 7.81/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_4320,c_40,c_39,c_4359]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2933,plain,
% 7.81/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5037,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_5029,c_2933]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_33,plain,
% 7.81/1.48      ( v5_pre_topc(X0,X1,X2)
% 7.81/1.48      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.81/1.48      | ~ v2_pre_topc(X1)
% 7.81/1.48      | ~ v2_pre_topc(X2)
% 7.81/1.48      | ~ l1_pre_topc(X1)
% 7.81/1.48      | ~ l1_pre_topc(X2)
% 7.81/1.48      | ~ v1_funct_1(X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f123]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2938,plain,
% 7.81/1.48      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 7.81/1.48      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 7.81/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.81/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.81/1.48      | v2_pre_topc(X1) != iProver_top
% 7.81/1.48      | v2_pre_topc(X2) != iProver_top
% 7.81/1.48      | l1_pre_topc(X1) != iProver_top
% 7.81/1.48      | l1_pre_topc(X2) != iProver_top
% 7.81/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6618,plain,
% 7.81/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.81/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.81/1.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.81/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.81/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_2934,c_2938]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_47,negated_conjecture,
% 7.81/1.48      ( v2_pre_topc(sK0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f104]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_48,plain,
% 7.81/1.48      ( v2_pre_topc(sK0) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_46,negated_conjecture,
% 7.81/1.48      ( l1_pre_topc(sK0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f105]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_49,plain,
% 7.81/1.48      ( l1_pre_topc(sK0) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_45,negated_conjecture,
% 7.81/1.48      ( v2_pre_topc(sK1) ),
% 7.81/1.48      inference(cnf_transformation,[],[f106]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_50,plain,
% 7.81/1.48      ( v2_pre_topc(sK1) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_44,negated_conjecture,
% 7.81/1.48      ( l1_pre_topc(sK1) ),
% 7.81/1.48      inference(cnf_transformation,[],[f107]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_51,plain,
% 7.81/1.48      ( l1_pre_topc(sK1) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_56,plain,
% 7.81/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_36,negated_conjecture,
% 7.81/1.48      ( v5_pre_topc(sK2,sK0,sK1)
% 7.81/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.81/1.48      inference(cnf_transformation,[],[f115]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2935,plain,
% 7.81/1.48      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
% 7.81/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3039,plain,
% 7.81/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.81/1.48      | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
% 7.81/1.48      inference(light_normalisation,[status(thm)],[c_2935,c_37]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3274,plain,
% 7.81/1.48      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.81/1.48      | ~ l1_pre_topc(sK0) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_29]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3275,plain,
% 7.81/1.48      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 7.81/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_3274]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_30,plain,
% 7.81/1.48      ( ~ v2_pre_topc(X0)
% 7.81/1.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.81/1.48      | ~ l1_pre_topc(X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f99]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3297,plain,
% 7.81/1.48      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(sK0) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_30]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3298,plain,
% 7.81/1.48      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 7.81/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_3297]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_28,plain,
% 7.81/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.81/1.48      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 7.81/1.48      inference(cnf_transformation,[],[f97]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3913,plain,
% 7.81/1.48      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.81/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_28]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3914,plain,
% 7.81/1.48      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 7.81/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_3913]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_32,plain,
% 7.81/1.48      ( ~ v5_pre_topc(X0,X1,X2)
% 7.81/1.48      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.81/1.48      | ~ v2_pre_topc(X1)
% 7.81/1.48      | ~ v2_pre_topc(X2)
% 7.81/1.48      | ~ l1_pre_topc(X1)
% 7.81/1.48      | ~ l1_pre_topc(X2)
% 7.81/1.48      | ~ v1_funct_1(X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f122]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3405,plain,
% 7.81/1.48      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
% 7.81/1.48      | ~ v5_pre_topc(X0,sK0,X1)
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 7.81/1.48      | ~ v2_pre_topc(X1)
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(X1)
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v1_funct_1(X0) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_32]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3736,plain,
% 7.81/1.48      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 7.81/1.48      | ~ v5_pre_topc(X0,sK0,sK1)
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.81/1.48      | ~ v2_pre_topc(sK1)
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(sK1)
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v1_funct_1(X0) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_3405]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4293,plain,
% 7.81/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 7.81/1.48      | ~ v5_pre_topc(sK3,sK0,sK1)
% 7.81/1.48      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 7.81/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.81/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 7.81/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.81/1.48      | ~ v2_pre_topc(sK1)
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(sK1)
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v1_funct_1(sK3) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_3736]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4294,plain,
% 7.81/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 7.81/1.48      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.81/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.81/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_4293]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_34,plain,
% 7.81/1.48      ( ~ v5_pre_topc(X0,X1,X2)
% 7.81/1.48      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.81/1.48      | ~ v2_pre_topc(X1)
% 7.81/1.48      | ~ v2_pre_topc(X2)
% 7.81/1.48      | ~ l1_pre_topc(X1)
% 7.81/1.48      | ~ l1_pre_topc(X2)
% 7.81/1.48      | ~ v1_funct_1(X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f124]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2937,plain,
% 7.81/1.48      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.81/1.48      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 7.81/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.81/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.81/1.48      | v2_pre_topc(X1) != iProver_top
% 7.81/1.48      | v2_pre_topc(X2) != iProver_top
% 7.81/1.48      | l1_pre_topc(X1) != iProver_top
% 7.81/1.48      | l1_pre_topc(X2) != iProver_top
% 7.81/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5782,plain,
% 7.81/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.81/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.81/1.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.81/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.81/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_2934,c_2937]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_35,negated_conjecture,
% 7.81/1.48      ( ~ v5_pre_topc(sK2,sK0,sK1)
% 7.81/1.48      | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.81/1.48      inference(cnf_transformation,[],[f116]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2936,plain,
% 7.81/1.48      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
% 7.81/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3044,plain,
% 7.81/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.81/1.48      | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
% 7.81/1.48      inference(light_normalisation,[status(thm)],[c_2936,c_37]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_31,plain,
% 7.81/1.48      ( v5_pre_topc(X0,X1,X2)
% 7.81/1.48      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.81/1.48      | ~ v2_pre_topc(X1)
% 7.81/1.48      | ~ v2_pre_topc(X2)
% 7.81/1.48      | ~ l1_pre_topc(X1)
% 7.81/1.48      | ~ l1_pre_topc(X2)
% 7.81/1.48      | ~ v1_funct_1(X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f121]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3395,plain,
% 7.81/1.48      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
% 7.81/1.48      | v5_pre_topc(X0,sK0,X1)
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 7.81/1.48      | ~ v2_pre_topc(X1)
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(X1)
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v1_funct_1(X0) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_31]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3696,plain,
% 7.81/1.48      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 7.81/1.48      | v5_pre_topc(X0,sK0,sK1)
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.81/1.48      | ~ v2_pre_topc(sK1)
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(sK1)
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v1_funct_1(X0) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_3395]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4269,plain,
% 7.81/1.48      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 7.81/1.48      | v5_pre_topc(sK3,sK0,sK1)
% 7.81/1.48      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 7.81/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.81/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 7.81/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.81/1.48      | ~ v2_pre_topc(sK1)
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(sK1)
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v1_funct_1(sK3) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_3696]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4270,plain,
% 7.81/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 7.81/1.48      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.81/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.81/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_4269]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6278,plain,
% 7.81/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_5782,c_48,c_49,c_50,c_51,c_55,c_56,c_3044,c_2975,
% 7.81/1.48                 c_2978,c_3275,c_3298,c_3914,c_4270]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6279,plain,
% 7.81/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 7.81/1.48      inference(renaming,[status(thm)],[c_6278]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_7332,plain,
% 7.81/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_6618,c_48,c_49,c_50,c_51,c_55,c_56,c_3039,c_2975,
% 7.81/1.48                 c_2978,c_3275,c_3298,c_3914,c_4294,c_6279]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_7333,plain,
% 7.81/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 7.81/1.48      inference(renaming,[status(thm)],[c_7332]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_7340,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_4526,c_7333]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2,plain,
% 7.81/1.48      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.81/1.48      inference(cnf_transformation,[],[f117]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_7344,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_7340,c_2]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4537,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) = iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_4526,c_2978]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4545,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_4537,c_2]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_8128,plain,
% 7.81/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_7344,c_4545]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_8129,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 7.81/1.48      inference(renaming,[status(thm)],[c_8128]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_8135,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_4526,c_8129]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_8359,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_5037,c_8135]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_8961,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_8359,c_8135]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_15,plain,
% 7.81/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2946,plain,
% 7.81/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.81/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5206,plain,
% 7.81/1.48      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 7.81/1.48      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_2,c_2946]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5340,plain,
% 7.81/1.48      ( k1_relset_1(X0,k1_xboole_0,sK3) = k1_relat_1(sK3)
% 7.81/1.48      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_4545,c_5206]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_24,plain,
% 7.81/1.48      ( v1_funct_2(X0,X1,X2)
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.48      | ~ v1_funct_1(X0)
% 7.81/1.48      | k1_relset_1(X1,X2,X0) != X1 ),
% 7.81/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2944,plain,
% 7.81/1.48      ( k1_relset_1(X0,X1,X2) != X0
% 7.81/1.48      | v1_funct_2(X2,X0,X1) = iProver_top
% 7.81/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.81/1.48      | v1_funct_1(X2) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_15846,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | k1_relat_1(sK3) != X0
% 7.81/1.48      | v1_funct_2(sK3,X0,k1_xboole_0) = iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_5340,c_2944]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_15847,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | k1_relat_1(sK3) != X0
% 7.81/1.48      | v1_funct_2(sK3,X0,k1_xboole_0) = iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.48      inference(light_normalisation,[status(thm)],[c_15846,c_2]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_15852,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | k1_relat_1(sK3) != X0
% 7.81/1.48      | v1_funct_2(sK3,X0,k1_xboole_0) = iProver_top ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_15847,c_55,c_4545]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_15861,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 7.81/1.48      inference(equality_resolution,[status(thm)],[c_15852]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_16021,plain,
% 7.81/1.48      ( u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_15220,c_8961,c_15861]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_16069,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 7.81/1.48      | u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_16021,c_5029]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_19422,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.81/1.48      | v5_pre_topc(X0,X1,sK1) != iProver_top
% 7.81/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
% 7.81/1.48      | v2_pre_topc(X1) != iProver_top
% 7.81/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.81/1.48      | l1_pre_topc(X1) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.81/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_16069,c_2937]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_19457,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.81/1.48      | v5_pre_topc(X0,X1,sK1) != iProver_top
% 7.81/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.81/1.48      | v2_pre_topc(X1) != iProver_top
% 7.81/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.81/1.48      | l1_pre_topc(X1) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.81/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_19422,c_2]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2939,plain,
% 7.81/1.48      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.81/1.48      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 7.81/1.48      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.81/1.48      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 7.81/1.48      | v2_pre_topc(X1) != iProver_top
% 7.81/1.48      | v2_pre_topc(X2) != iProver_top
% 7.81/1.48      | l1_pre_topc(X1) != iProver_top
% 7.81/1.48      | l1_pre_topc(X2) != iProver_top
% 7.81/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_7666,plain,
% 7.81/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.81/1.48      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.81/1.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.81/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.81/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_2934,c_2939]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_57,plain,
% 7.81/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3271,plain,
% 7.81/1.48      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.81/1.48      | ~ l1_pre_topc(sK1) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_29]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3272,plain,
% 7.81/1.48      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 7.81/1.48      | l1_pre_topc(sK1) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_3271]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3294,plain,
% 7.81/1.48      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.81/1.48      | ~ v2_pre_topc(sK1)
% 7.81/1.48      | ~ l1_pre_topc(sK1) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_30]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3295,plain,
% 7.81/1.48      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.81/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK1) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_3294]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3440,plain,
% 7.81/1.48      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.81/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_28]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3441,plain,
% 7.81/1.48      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 7.81/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_3440]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3415,plain,
% 7.81/1.48      ( v5_pre_topc(X0,sK0,X1)
% 7.81/1.48      | ~ v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 7.81/1.48      | ~ v2_pre_topc(X1)
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(X1)
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v1_funct_1(X0) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_33]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3776,plain,
% 7.81/1.48      ( ~ v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.81/1.48      | v5_pre_topc(X0,sK0,sK1)
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.81/1.48      | ~ v2_pre_topc(sK1)
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(sK1)
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v1_funct_1(X0) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_3415]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4371,plain,
% 7.81/1.48      ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.81/1.48      | v5_pre_topc(sK3,sK0,sK1)
% 7.81/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.81/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.81/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.81/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.81/1.48      | ~ v2_pre_topc(sK1)
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(sK1)
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v1_funct_1(sK3) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_3776]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4372,plain,
% 7.81/1.48      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.81/1.48      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.81/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.81/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_4371]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3435,plain,
% 7.81/1.48      ( ~ v5_pre_topc(X0,sK0,X1)
% 7.81/1.48      | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 7.81/1.48      | ~ v2_pre_topc(X1)
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(X1)
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v1_funct_1(X0) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_34]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3823,plain,
% 7.81/1.48      ( v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.81/1.48      | ~ v5_pre_topc(X0,sK0,sK1)
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.81/1.48      | ~ v2_pre_topc(sK1)
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(sK1)
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v1_funct_1(X0) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_3435]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4395,plain,
% 7.81/1.48      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.81/1.48      | ~ v5_pre_topc(sK3,sK0,sK1)
% 7.81/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.81/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.81/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.81/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.81/1.48      | ~ v2_pre_topc(sK1)
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(sK1)
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v1_funct_1(sK3) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_3823]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4396,plain,
% 7.81/1.48      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.81/1.48      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.81/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.81/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_4395]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3706,plain,
% 7.81/1.48      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.81/1.48      | v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.81/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.81/1.48      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v1_funct_1(X0) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_3395]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4986,plain,
% 7.81/1.48      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.81/1.48      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.81/1.48      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.81/1.48      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 7.81/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.81/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 7.81/1.48      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v1_funct_1(sK3) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_3706]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4987,plain,
% 7.81/1.48      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.81/1.48      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.81/1.48      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.81/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.81/1.48      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_4986]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_8321,plain,
% 7.81/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_7666,c_48,c_49,c_50,c_51,c_55,c_56,c_57,c_3039,c_3044,
% 7.81/1.48                 c_2975,c_2978,c_3272,c_3295,c_3441,c_4372,c_4396,c_4987]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_8322,plain,
% 7.81/1.48      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 7.81/1.48      inference(renaming,[status(thm)],[c_8321]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_8325,plain,
% 7.81/1.48      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_8322,c_48,c_49,c_50,c_51,c_55,c_56,c_57,c_3039,c_2975,
% 7.81/1.48                 c_2978,c_3272,c_3295,c_3441,c_4396,c_4987]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_8332,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_5029,c_8325]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_8343,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_8332,c_2]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5036,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) = iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_5029,c_2934]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5044,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_5036,c_2]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_9863,plain,
% 7.81/1.48      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 7.81/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_8343,c_5044]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_9864,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 7.81/1.48      inference(renaming,[status(thm)],[c_9863]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_9869,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_5029,c_9864]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_16040,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_16021,c_9869]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5339,plain,
% 7.81/1.48      ( k1_relset_1(X0,k1_xboole_0,sK3) = k1_relat_1(sK3)
% 7.81/1.48      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_5044,c_5206]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_20252,plain,
% 7.81/1.48      ( k1_relset_1(X0,k1_xboole_0,sK3) = k1_relat_1(sK3)
% 7.81/1.48      | u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.81/1.48      inference(light_normalisation,[status(thm)],[c_5339,c_16021]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_20276,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | k1_relat_1(sK3) != X0
% 7.81/1.48      | v1_funct_2(sK3,X0,k1_xboole_0) = iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_20252,c_2944]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_20282,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | k1_relat_1(sK3) != X0
% 7.81/1.48      | v1_funct_2(sK3,X0,k1_xboole_0) = iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.81/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.48      inference(light_normalisation,[status(thm)],[c_20276,c_2]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_16067,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_16021,c_5044]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_20617,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | k1_relat_1(sK3) != X0
% 7.81/1.48      | v1_funct_2(sK3,X0,k1_xboole_0) = iProver_top ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_20282,c_55,c_16067]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_20626,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 7.81/1.48      | v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 7.81/1.48      inference(equality_resolution,[status(thm)],[c_20617]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_20714,plain,
% 7.81/1.48      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_19457,c_16040,c_20626]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_16051,plain,
% 7.81/1.48      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_16021,c_7333]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_20719,plain,
% 7.81/1.48      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
% 7.81/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_20714,c_16051]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_16076,plain,
% 7.81/1.48      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_16021,c_2975]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_16075,plain,
% 7.81/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_16021,c_2978]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(contradiction,plain,
% 7.81/1.48      ( $false ),
% 7.81/1.48      inference(minisat,[status(thm)],[c_20719,c_16076,c_16075]) ).
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.81/1.48  
% 7.81/1.48  ------                               Statistics
% 7.81/1.48  
% 7.81/1.48  ------ General
% 7.81/1.48  
% 7.81/1.48  abstr_ref_over_cycles:                  0
% 7.81/1.48  abstr_ref_under_cycles:                 0
% 7.81/1.48  gc_basic_clause_elim:                   0
% 7.81/1.48  forced_gc_time:                         0
% 7.81/1.48  parsing_time:                           0.012
% 7.81/1.48  unif_index_cands_time:                  0.
% 7.81/1.48  unif_index_add_time:                    0.
% 7.81/1.48  orderings_time:                         0.
% 7.81/1.48  out_proof_time:                         0.019
% 7.81/1.48  total_time:                             0.648
% 7.81/1.48  num_of_symbols:                         54
% 7.81/1.48  num_of_terms:                           15449
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing
% 7.81/1.48  
% 7.81/1.48  num_of_splits:                          0
% 7.81/1.48  num_of_split_atoms:                     0
% 7.81/1.48  num_of_reused_defs:                     0
% 7.81/1.48  num_eq_ax_congr_red:                    17
% 7.81/1.48  num_of_sem_filtered_clauses:            1
% 7.81/1.48  num_of_subtypes:                        0
% 7.81/1.48  monotx_restored_types:                  0
% 7.81/1.48  sat_num_of_epr_types:                   0
% 7.81/1.48  sat_num_of_non_cyclic_types:            0
% 7.81/1.48  sat_guarded_non_collapsed_types:        0
% 7.81/1.48  num_pure_diseq_elim:                    0
% 7.81/1.48  simp_replaced_by:                       0
% 7.81/1.48  res_preprocessed:                       183
% 7.81/1.48  prep_upred:                             0
% 7.81/1.48  prep_unflattend:                        42
% 7.81/1.48  smt_new_axioms:                         0
% 7.81/1.48  pred_elim_cands:                        7
% 7.81/1.48  pred_elim:                              4
% 7.81/1.48  pred_elim_cl:                           6
% 7.81/1.48  pred_elim_cycles:                       7
% 7.81/1.48  merged_defs:                            8
% 7.81/1.48  merged_defs_ncl:                        0
% 7.81/1.48  bin_hyper_res:                          8
% 7.81/1.48  prep_cycles:                            4
% 7.81/1.48  pred_elim_time:                         0.028
% 7.81/1.48  splitting_time:                         0.
% 7.81/1.48  sem_filter_time:                        0.
% 7.81/1.48  monotx_time:                            0.001
% 7.81/1.48  subtype_inf_time:                       0.
% 7.81/1.48  
% 7.81/1.48  ------ Problem properties
% 7.81/1.48  
% 7.81/1.48  clauses:                                37
% 7.81/1.48  conjectures:                            13
% 7.81/1.48  epr:                                    11
% 7.81/1.48  horn:                                   31
% 7.81/1.48  ground:                                 14
% 7.81/1.48  unary:                                  15
% 7.81/1.48  binary:                                 5
% 7.81/1.48  lits:                                   119
% 7.81/1.48  lits_eq:                                13
% 7.81/1.48  fd_pure:                                0
% 7.81/1.48  fd_pseudo:                              0
% 7.81/1.48  fd_cond:                                1
% 7.81/1.48  fd_pseudo_cond:                         3
% 7.81/1.48  ac_symbols:                             0
% 7.81/1.48  
% 7.81/1.48  ------ Propositional Solver
% 7.81/1.48  
% 7.81/1.48  prop_solver_calls:                      29
% 7.81/1.48  prop_fast_solver_calls:                 2400
% 7.81/1.48  smt_solver_calls:                       0
% 7.81/1.48  smt_fast_solver_calls:                  0
% 7.81/1.48  prop_num_of_clauses:                    6786
% 7.81/1.48  prop_preprocess_simplified:             15509
% 7.81/1.48  prop_fo_subsumed:                       145
% 7.81/1.48  prop_solver_time:                       0.
% 7.81/1.48  smt_solver_time:                        0.
% 7.81/1.48  smt_fast_solver_time:                   0.
% 7.81/1.48  prop_fast_solver_time:                  0.
% 7.81/1.48  prop_unsat_core_time:                   0.
% 7.81/1.48  
% 7.81/1.48  ------ QBF
% 7.81/1.48  
% 7.81/1.48  qbf_q_res:                              0
% 7.81/1.48  qbf_num_tautologies:                    0
% 7.81/1.48  qbf_prep_cycles:                        0
% 7.81/1.48  
% 7.81/1.48  ------ BMC1
% 7.81/1.48  
% 7.81/1.48  bmc1_current_bound:                     -1
% 7.81/1.48  bmc1_last_solved_bound:                 -1
% 7.81/1.48  bmc1_unsat_core_size:                   -1
% 7.81/1.48  bmc1_unsat_core_parents_size:           -1
% 7.81/1.48  bmc1_merge_next_fun:                    0
% 7.81/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.81/1.48  
% 7.81/1.48  ------ Instantiation
% 7.81/1.48  
% 7.81/1.48  inst_num_of_clauses:                    1765
% 7.81/1.48  inst_num_in_passive:                    1010
% 7.81/1.48  inst_num_in_active:                     753
% 7.81/1.48  inst_num_in_unprocessed:                2
% 7.81/1.48  inst_num_of_loops:                      790
% 7.81/1.48  inst_num_of_learning_restarts:          0
% 7.81/1.48  inst_num_moves_active_passive:          35
% 7.81/1.48  inst_lit_activity:                      0
% 7.81/1.48  inst_lit_activity_moves:                0
% 7.81/1.48  inst_num_tautologies:                   0
% 7.81/1.48  inst_num_prop_implied:                  0
% 7.81/1.48  inst_num_existing_simplified:           0
% 7.81/1.48  inst_num_eq_res_simplified:             0
% 7.81/1.48  inst_num_child_elim:                    0
% 7.81/1.48  inst_num_of_dismatching_blockings:      295
% 7.81/1.48  inst_num_of_non_proper_insts:           1703
% 7.81/1.48  inst_num_of_duplicates:                 0
% 7.81/1.48  inst_inst_num_from_inst_to_res:         0
% 7.81/1.48  inst_dismatching_checking_time:         0.
% 7.81/1.48  
% 7.81/1.48  ------ Resolution
% 7.81/1.48  
% 7.81/1.48  res_num_of_clauses:                     0
% 7.81/1.48  res_num_in_passive:                     0
% 7.81/1.48  res_num_in_active:                      0
% 7.81/1.48  res_num_of_loops:                       187
% 7.81/1.48  res_forward_subset_subsumed:            37
% 7.81/1.48  res_backward_subset_subsumed:           0
% 7.81/1.48  res_forward_subsumed:                   0
% 7.81/1.48  res_backward_subsumed:                  0
% 7.81/1.48  res_forward_subsumption_resolution:     1
% 7.81/1.48  res_backward_subsumption_resolution:    0
% 7.81/1.48  res_clause_to_clause_subsumption:       1039
% 7.81/1.48  res_orphan_elimination:                 0
% 7.81/1.48  res_tautology_del:                      117
% 7.81/1.48  res_num_eq_res_simplified:              0
% 7.81/1.48  res_num_sel_changes:                    0
% 7.81/1.48  res_moves_from_active_to_pass:          0
% 7.81/1.48  
% 7.81/1.48  ------ Superposition
% 7.81/1.48  
% 7.81/1.48  sup_time_total:                         0.
% 7.81/1.48  sup_time_generating:                    0.
% 7.81/1.48  sup_time_sim_full:                      0.
% 7.81/1.48  sup_time_sim_immed:                     0.
% 7.81/1.48  
% 7.81/1.48  sup_num_of_clauses:                     206
% 7.81/1.48  sup_num_in_active:                      62
% 7.81/1.48  sup_num_in_passive:                     144
% 7.81/1.48  sup_num_of_loops:                       156
% 7.81/1.48  sup_fw_superposition:                   363
% 7.81/1.48  sup_bw_superposition:                   240
% 7.81/1.48  sup_immediate_simplified:               219
% 7.81/1.48  sup_given_eliminated:                   1
% 7.81/1.48  comparisons_done:                       0
% 7.81/1.48  comparisons_avoided:                    30
% 7.81/1.48  
% 7.81/1.48  ------ Simplifications
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  sim_fw_subset_subsumed:                 136
% 7.81/1.48  sim_bw_subset_subsumed:                 122
% 7.81/1.48  sim_fw_subsumed:                        14
% 7.81/1.48  sim_bw_subsumed:                        21
% 7.81/1.48  sim_fw_subsumption_res:                 2
% 7.81/1.48  sim_bw_subsumption_res:                 0
% 7.81/1.48  sim_tautology_del:                      12
% 7.81/1.48  sim_eq_tautology_del:                   29
% 7.81/1.48  sim_eq_res_simp:                        0
% 7.81/1.48  sim_fw_demodulated:                     41
% 7.81/1.48  sim_bw_demodulated:                     61
% 7.81/1.48  sim_light_normalised:                   16
% 7.81/1.48  sim_joinable_taut:                      0
% 7.81/1.48  sim_joinable_simp:                      0
% 7.81/1.48  sim_ac_normalised:                      0
% 7.81/1.48  sim_smt_subsumption:                    0
% 7.81/1.48  
%------------------------------------------------------------------------------
