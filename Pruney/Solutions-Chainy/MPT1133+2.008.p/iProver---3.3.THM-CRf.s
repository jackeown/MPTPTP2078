%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:49 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  218 (5625 expanded)
%              Number of clauses        :  126 ( 972 expanded)
%              Number of leaves         :   18 (1754 expanded)
%              Depth                    :   28
%              Number of atoms          : 1039 (68896 expanded)
%              Number of equality atoms :  343 (6847 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f132,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f118,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f72])).

fof(f24,conjecture,(
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

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f25])).

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
    inference(flattening,[],[f53])).

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
    inference(nnf_transformation,[],[f54])).

fof(f67,plain,(
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
    inference(flattening,[],[f66])).

fof(f71,plain,(
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

fof(f70,plain,(
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

fof(f69,plain,(
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

fof(f68,plain,
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

fof(f72,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f67,f71,f70,f69,f68])).

fof(f122,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f72])).

fof(f128,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f118,f122])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f36])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f116,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f72])).

fof(f130,plain,(
    v1_funct_1(sK5) ),
    inference(definition_unfolding,[],[f116,f122])).

fof(f121,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f72])).

fof(f18,axiom,(
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

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

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
    inference(flattening,[],[f43])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f120,plain,(
    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f72])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f117,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f72])).

fof(f129,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(definition_unfolding,[],[f117,f122])).

fof(f23,axiom,(
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

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f23])).

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
    inference(flattening,[],[f51])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f52])).

fof(f110,plain,(
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
    inference(cnf_transformation,[],[f65])).

fof(f140,plain,(
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
    inference(equality_resolution,[],[f110])).

fof(f112,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f113,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f114,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f72])).

fof(f115,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f72])).

fof(f123,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f72])).

fof(f127,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK2,sK3) ),
    inference(definition_unfolding,[],[f123,f122])).

fof(f124,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f72])).

fof(f126,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK5,sK2,sK3) ),
    inference(definition_unfolding,[],[f124,f122])).

fof(f22,axiom,(
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

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f22])).

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
    inference(flattening,[],[f49])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f50])).

fof(f109,plain,(
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
    inference(cnf_transformation,[],[f64])).

fof(f137,plain,(
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
    inference(equality_resolution,[],[f109])).

fof(f111,plain,(
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
    inference(cnf_transformation,[],[f65])).

fof(f139,plain,(
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
    inference(equality_resolution,[],[f111])).

fof(f108,plain,(
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
    inference(cnf_transformation,[],[f64])).

fof(f138,plain,(
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
    inference(equality_resolution,[],[f108])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f47,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f107,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f105,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f106,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f57])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f79])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f135,plain,(
    ! [X1] :
      ( v1_partfun1(X1,k1_relat_1(X1))
      | ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f94])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_3956,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_3927,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3952,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6751,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK3)))) = iProver_top
    | r1_tarski(k1_relat_1(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3927,c_3952])).

cnf(c_18,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3950,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7435,plain,
    ( v1_funct_2(sK5,X0,u1_struct_0(sK3)) = iProver_top
    | v1_partfun1(sK5,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6751,c_3950])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_54,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_7618,plain,
    ( r1_tarski(k1_relat_1(sK5),X0) != iProver_top
    | v1_partfun1(sK5,X0) != iProver_top
    | v1_funct_2(sK5,X0,u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7435,c_54])).

cnf(c_7619,plain,
    ( v1_funct_2(sK5,X0,u1_struct_0(sK3)) = iProver_top
    | v1_partfun1(sK5,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7618])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_3930,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3940,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_partfun1(X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8145,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3930,c_3940])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_58,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_8402,plain,
    ( v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8145,c_54,c_58])).

cnf(c_8403,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_8402])).

cnf(c_21,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3948,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8406,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v4_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_8403,c_3948])).

cnf(c_59,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4972,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4973,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4972])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3953,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6371,plain,
    ( v4_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3930,c_3953])).

cnf(c_9274,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8406,c_59,c_4973,c_6371])).

cnf(c_3929,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_9312,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9274,c_3929])).

cnf(c_8146,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_partfun1(sK5,u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3927,c_3940])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_55,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_8335,plain,
    ( v1_partfun1(sK5,u1_struct_0(sK2)) = iProver_top
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8146,c_54,c_55])).

cnf(c_8336,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v1_partfun1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8335])).

cnf(c_8339,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(sK2) = k1_relat_1(sK5)
    | v4_relat_1(sK5,u1_struct_0(sK2)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_8336,c_3948])).

cnf(c_6372,plain,
    ( v4_relat_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3927,c_3953])).

cnf(c_8460,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8339,c_59,c_4973,c_6372])).

cnf(c_37,plain,
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
    inference(cnf_transformation,[],[f140])).

cnf(c_3933,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5273,plain,
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
    inference(superposition,[status(thm)],[c_3930,c_3933])).

cnf(c_49,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_50,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_48,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_51,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_52,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_53,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_56,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_39,negated_conjecture,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_60,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_61,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_34,plain,
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
    inference(cnf_transformation,[],[f137])).

cnf(c_4009,plain,
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
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_4013,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4009])).

cnf(c_36,plain,
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
    inference(cnf_transformation,[],[f139])).

cnf(c_4023,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_4024,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4023])).

cnf(c_35,plain,
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
    inference(cnf_transformation,[],[f138])).

cnf(c_4028,plain,
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
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_4029,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4028])).

cnf(c_33,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_4071,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_4072,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4071])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_4156,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_4157,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4156])).

cnf(c_32,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_4216,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_4217,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4216])).

cnf(c_5629,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5273,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,c_60,c_61,c_4013,c_4024,c_4029,c_4072,c_4157,c_4217])).

cnf(c_5630,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5629])).

cnf(c_5633,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5630,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,c_60,c_4024,c_4029,c_4072,c_4157,c_4217])).

cnf(c_8492,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8460,c_5633])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_8503,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8492,c_4])).

cnf(c_8499,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8460,c_3927])).

cnf(c_8501,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8499,c_4])).

cnf(c_8930,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8503,c_8501])).

cnf(c_8931,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8930])).

cnf(c_8935,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8460,c_8931])).

cnf(c_9806,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_9312,c_8935])).

cnf(c_9899,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9806,c_8931])).

cnf(c_10444,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_partfun1(sK5,k1_relat_1(sK5)) != iProver_top
    | r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7619,c_9899])).

cnf(c_6996,plain,
    ( v4_relat_1(sK5,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6751,c_3953])).

cnf(c_7174,plain,
    ( v4_relat_1(sK5,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3956,c_6996])).

cnf(c_20,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v4_relat_1(X0,k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_3949,plain,
    ( v1_partfun1(X0,k1_relat_1(X0)) = iProver_top
    | v4_relat_1(X0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8257,plain,
    ( v1_partfun1(sK5,k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7174,c_3949])).

cnf(c_10491,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10444,c_59,c_4973,c_8257])).

cnf(c_10495,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3956,c_10491])).

cnf(c_6750,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top
    | r1_tarski(k1_relat_1(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3930,c_3952])).

cnf(c_3935,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6647,plain,
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
    inference(superposition,[status(thm)],[c_3930,c_3935])).

cnf(c_4010,plain,
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
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_4011,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4010])).

cnf(c_4036,plain,
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
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_4040,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4036])).

cnf(c_4042,plain,
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
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_4043,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4042])).

cnf(c_4084,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_4085,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4084])).

cnf(c_4166,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_4167,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4166])).

cnf(c_4224,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_4225,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4224])).

cnf(c_7077,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6647,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,c_60,c_61,c_4011,c_4040,c_4043,c_4085,c_4167,c_4225])).

cnf(c_7078,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7077])).

cnf(c_7081,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7078,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,c_60,c_4040,c_4043,c_4085,c_4167,c_4225])).

cnf(c_7086,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | r1_tarski(k1_relat_1(sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6750,c_7081])).

cnf(c_11495,plain,
    ( v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10495,c_7086])).

cnf(c_7434,plain,
    ( v1_funct_2(sK5,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top
    | v1_partfun1(sK5,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6750,c_3950])).

cnf(c_7715,plain,
    ( r1_tarski(k1_relat_1(sK5),X0) != iProver_top
    | v1_partfun1(sK5,X0) != iProver_top
    | v1_funct_2(sK5,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7434,c_54])).

cnf(c_7716,plain,
    ( v1_funct_2(sK5,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top
    | v1_partfun1(sK5,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7715])).

cnf(c_7722,plain,
    ( v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7716,c_7086])).

cnf(c_11486,plain,
    ( v1_partfun1(sK5,k1_relat_1(sK5)) != iProver_top
    | r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10495,c_7722])).

cnf(c_12632,plain,
    ( r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11495,c_59,c_4973,c_8257,c_11486])).

cnf(c_12636,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3956,c_12632])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n017.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 19:48:46 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.80/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/0.96  
% 3.80/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.80/0.96  
% 3.80/0.96  ------  iProver source info
% 3.80/0.96  
% 3.80/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.80/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.80/0.96  git: non_committed_changes: false
% 3.80/0.96  git: last_make_outside_of_git: false
% 3.80/0.96  
% 3.80/0.96  ------ 
% 3.80/0.96  
% 3.80/0.96  ------ Input Options
% 3.80/0.96  
% 3.80/0.96  --out_options                           all
% 3.80/0.96  --tptp_safe_out                         true
% 3.80/0.96  --problem_path                          ""
% 3.80/0.96  --include_path                          ""
% 3.80/0.96  --clausifier                            res/vclausify_rel
% 3.80/0.96  --clausifier_options                    ""
% 3.80/0.96  --stdin                                 false
% 3.80/0.96  --stats_out                             all
% 3.80/0.96  
% 3.80/0.96  ------ General Options
% 3.80/0.96  
% 3.80/0.96  --fof                                   false
% 3.80/0.96  --time_out_real                         305.
% 3.80/0.96  --time_out_virtual                      -1.
% 3.80/0.96  --symbol_type_check                     false
% 3.80/0.96  --clausify_out                          false
% 3.80/0.96  --sig_cnt_out                           false
% 3.80/0.96  --trig_cnt_out                          false
% 3.80/0.96  --trig_cnt_out_tolerance                1.
% 3.80/0.96  --trig_cnt_out_sk_spl                   false
% 3.80/0.96  --abstr_cl_out                          false
% 3.80/0.96  
% 3.80/0.96  ------ Global Options
% 3.80/0.96  
% 3.80/0.96  --schedule                              default
% 3.80/0.96  --add_important_lit                     false
% 3.80/0.96  --prop_solver_per_cl                    1000
% 3.80/0.96  --min_unsat_core                        false
% 3.80/0.96  --soft_assumptions                      false
% 3.80/0.96  --soft_lemma_size                       3
% 3.80/0.96  --prop_impl_unit_size                   0
% 3.80/0.96  --prop_impl_unit                        []
% 3.80/0.96  --share_sel_clauses                     true
% 3.80/0.96  --reset_solvers                         false
% 3.80/0.96  --bc_imp_inh                            [conj_cone]
% 3.80/0.96  --conj_cone_tolerance                   3.
% 3.80/0.96  --extra_neg_conj                        none
% 3.80/0.96  --large_theory_mode                     true
% 3.80/0.96  --prolific_symb_bound                   200
% 3.80/0.96  --lt_threshold                          2000
% 3.80/0.96  --clause_weak_htbl                      true
% 3.80/0.96  --gc_record_bc_elim                     false
% 3.80/0.96  
% 3.80/0.96  ------ Preprocessing Options
% 3.80/0.96  
% 3.80/0.96  --preprocessing_flag                    true
% 3.80/0.96  --time_out_prep_mult                    0.1
% 3.80/0.96  --splitting_mode                        input
% 3.80/0.96  --splitting_grd                         true
% 3.80/0.96  --splitting_cvd                         false
% 3.80/0.96  --splitting_cvd_svl                     false
% 3.80/0.96  --splitting_nvd                         32
% 3.80/0.96  --sub_typing                            true
% 3.80/0.96  --prep_gs_sim                           true
% 3.80/0.96  --prep_unflatten                        true
% 3.80/0.96  --prep_res_sim                          true
% 3.80/0.96  --prep_upred                            true
% 3.80/0.96  --prep_sem_filter                       exhaustive
% 3.80/0.96  --prep_sem_filter_out                   false
% 3.80/0.96  --pred_elim                             true
% 3.80/0.96  --res_sim_input                         true
% 3.80/0.96  --eq_ax_congr_red                       true
% 3.80/0.96  --pure_diseq_elim                       true
% 3.80/0.96  --brand_transform                       false
% 3.80/0.96  --non_eq_to_eq                          false
% 3.80/0.96  --prep_def_merge                        true
% 3.80/0.96  --prep_def_merge_prop_impl              false
% 3.80/0.96  --prep_def_merge_mbd                    true
% 3.80/0.96  --prep_def_merge_tr_red                 false
% 3.80/0.96  --prep_def_merge_tr_cl                  false
% 3.80/0.96  --smt_preprocessing                     true
% 3.80/0.96  --smt_ac_axioms                         fast
% 3.80/0.96  --preprocessed_out                      false
% 3.80/0.96  --preprocessed_stats                    false
% 3.80/0.96  
% 3.80/0.96  ------ Abstraction refinement Options
% 3.80/0.96  
% 3.80/0.96  --abstr_ref                             []
% 3.80/0.96  --abstr_ref_prep                        false
% 3.80/0.96  --abstr_ref_until_sat                   false
% 3.80/0.96  --abstr_ref_sig_restrict                funpre
% 3.80/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/0.96  --abstr_ref_under                       []
% 3.80/0.96  
% 3.80/0.96  ------ SAT Options
% 3.80/0.96  
% 3.80/0.96  --sat_mode                              false
% 3.80/0.96  --sat_fm_restart_options                ""
% 3.80/0.96  --sat_gr_def                            false
% 3.80/0.96  --sat_epr_types                         true
% 3.80/0.96  --sat_non_cyclic_types                  false
% 3.80/0.96  --sat_finite_models                     false
% 3.80/0.96  --sat_fm_lemmas                         false
% 3.80/0.96  --sat_fm_prep                           false
% 3.80/0.96  --sat_fm_uc_incr                        true
% 3.80/0.96  --sat_out_model                         small
% 3.80/0.96  --sat_out_clauses                       false
% 3.80/0.96  
% 3.80/0.96  ------ QBF Options
% 3.80/0.96  
% 3.80/0.96  --qbf_mode                              false
% 3.80/0.96  --qbf_elim_univ                         false
% 3.80/0.96  --qbf_dom_inst                          none
% 3.80/0.96  --qbf_dom_pre_inst                      false
% 3.80/0.96  --qbf_sk_in                             false
% 3.80/0.96  --qbf_pred_elim                         true
% 3.80/0.96  --qbf_split                             512
% 3.80/0.96  
% 3.80/0.96  ------ BMC1 Options
% 3.80/0.96  
% 3.80/0.96  --bmc1_incremental                      false
% 3.80/0.96  --bmc1_axioms                           reachable_all
% 3.80/0.96  --bmc1_min_bound                        0
% 3.80/0.96  --bmc1_max_bound                        -1
% 3.80/0.96  --bmc1_max_bound_default                -1
% 3.80/0.96  --bmc1_symbol_reachability              true
% 3.80/0.96  --bmc1_property_lemmas                  false
% 3.80/0.96  --bmc1_k_induction                      false
% 3.80/0.96  --bmc1_non_equiv_states                 false
% 3.80/0.96  --bmc1_deadlock                         false
% 3.80/0.96  --bmc1_ucm                              false
% 3.80/0.96  --bmc1_add_unsat_core                   none
% 3.80/0.96  --bmc1_unsat_core_children              false
% 3.80/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/0.96  --bmc1_out_stat                         full
% 3.80/0.96  --bmc1_ground_init                      false
% 3.80/0.96  --bmc1_pre_inst_next_state              false
% 3.80/0.96  --bmc1_pre_inst_state                   false
% 3.80/0.96  --bmc1_pre_inst_reach_state             false
% 3.80/0.96  --bmc1_out_unsat_core                   false
% 3.80/0.96  --bmc1_aig_witness_out                  false
% 3.80/0.96  --bmc1_verbose                          false
% 3.80/0.96  --bmc1_dump_clauses_tptp                false
% 3.80/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.80/0.96  --bmc1_dump_file                        -
% 3.80/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.80/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.80/0.96  --bmc1_ucm_extend_mode                  1
% 3.80/0.96  --bmc1_ucm_init_mode                    2
% 3.80/0.96  --bmc1_ucm_cone_mode                    none
% 3.80/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.80/0.96  --bmc1_ucm_relax_model                  4
% 3.80/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.80/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/0.96  --bmc1_ucm_layered_model                none
% 3.80/0.96  --bmc1_ucm_max_lemma_size               10
% 3.80/0.96  
% 3.80/0.96  ------ AIG Options
% 3.80/0.96  
% 3.80/0.96  --aig_mode                              false
% 3.80/0.96  
% 3.80/0.96  ------ Instantiation Options
% 3.80/0.96  
% 3.80/0.96  --instantiation_flag                    true
% 3.80/0.96  --inst_sos_flag                         true
% 3.80/0.96  --inst_sos_phase                        true
% 3.80/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/0.96  --inst_lit_sel_side                     num_symb
% 3.80/0.96  --inst_solver_per_active                1400
% 3.80/0.96  --inst_solver_calls_frac                1.
% 3.80/0.96  --inst_passive_queue_type               priority_queues
% 3.80/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/0.96  --inst_passive_queues_freq              [25;2]
% 3.80/0.96  --inst_dismatching                      true
% 3.80/0.96  --inst_eager_unprocessed_to_passive     true
% 3.80/0.96  --inst_prop_sim_given                   true
% 3.80/0.96  --inst_prop_sim_new                     false
% 3.80/0.96  --inst_subs_new                         false
% 3.80/0.96  --inst_eq_res_simp                      false
% 3.80/0.96  --inst_subs_given                       false
% 3.80/0.96  --inst_orphan_elimination               true
% 3.80/0.96  --inst_learning_loop_flag               true
% 3.80/0.96  --inst_learning_start                   3000
% 3.80/0.96  --inst_learning_factor                  2
% 3.80/0.96  --inst_start_prop_sim_after_learn       3
% 3.80/0.96  --inst_sel_renew                        solver
% 3.80/0.96  --inst_lit_activity_flag                true
% 3.80/0.96  --inst_restr_to_given                   false
% 3.80/0.96  --inst_activity_threshold               500
% 3.80/0.96  --inst_out_proof                        true
% 3.80/0.96  
% 3.80/0.96  ------ Resolution Options
% 3.80/0.96  
% 3.80/0.96  --resolution_flag                       true
% 3.80/0.96  --res_lit_sel                           adaptive
% 3.80/0.96  --res_lit_sel_side                      none
% 3.80/0.96  --res_ordering                          kbo
% 3.80/0.96  --res_to_prop_solver                    active
% 3.80/0.96  --res_prop_simpl_new                    false
% 3.80/0.96  --res_prop_simpl_given                  true
% 3.80/0.96  --res_passive_queue_type                priority_queues
% 3.80/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/0.96  --res_passive_queues_freq               [15;5]
% 3.80/0.96  --res_forward_subs                      full
% 3.80/0.96  --res_backward_subs                     full
% 3.80/0.96  --res_forward_subs_resolution           true
% 3.80/0.96  --res_backward_subs_resolution          true
% 3.80/0.96  --res_orphan_elimination                true
% 3.80/0.96  --res_time_limit                        2.
% 3.80/0.96  --res_out_proof                         true
% 3.80/0.96  
% 3.80/0.96  ------ Superposition Options
% 3.80/0.96  
% 3.80/0.96  --superposition_flag                    true
% 3.80/0.96  --sup_passive_queue_type                priority_queues
% 3.80/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.80/0.96  --demod_completeness_check              fast
% 3.80/0.96  --demod_use_ground                      true
% 3.80/0.96  --sup_to_prop_solver                    passive
% 3.80/0.96  --sup_prop_simpl_new                    true
% 3.80/0.96  --sup_prop_simpl_given                  true
% 3.80/0.96  --sup_fun_splitting                     true
% 3.80/0.96  --sup_smt_interval                      50000
% 3.80/0.96  
% 3.80/0.96  ------ Superposition Simplification Setup
% 3.80/0.96  
% 3.80/0.96  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.80/0.96  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.80/0.96  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.80/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.80/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.80/0.96  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.80/0.96  --sup_immed_triv                        [TrivRules]
% 3.80/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.96  --sup_immed_bw_main                     []
% 3.80/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.80/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.96  --sup_input_bw                          []
% 3.80/0.96  
% 3.80/0.96  ------ Combination Options
% 3.80/0.96  
% 3.80/0.96  --comb_res_mult                         3
% 3.80/0.96  --comb_sup_mult                         2
% 3.80/0.96  --comb_inst_mult                        10
% 3.80/0.96  
% 3.80/0.96  ------ Debug Options
% 3.80/0.96  
% 3.80/0.96  --dbg_backtrace                         false
% 3.80/0.96  --dbg_dump_prop_clauses                 false
% 3.80/0.96  --dbg_dump_prop_clauses_file            -
% 3.80/0.96  --dbg_out_stat                          false
% 3.80/0.96  ------ Parsing...
% 3.80/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.80/0.96  
% 3.80/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.80/0.96  
% 3.80/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.80/0.96  
% 3.80/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.80/0.96  ------ Proving...
% 3.80/0.96  ------ Problem Properties 
% 3.80/0.96  
% 3.80/0.96  
% 3.80/0.96  clauses                                 44
% 3.80/0.96  conjectures                             11
% 3.80/0.96  EPR                                     8
% 3.80/0.96  Horn                                    40
% 3.80/0.96  unary                                   21
% 3.80/0.96  binary                                  9
% 3.80/0.96  lits                                    118
% 3.80/0.96  lits eq                                 14
% 3.80/0.96  fd_pure                                 0
% 3.80/0.96  fd_pseudo                               0
% 3.80/0.96  fd_cond                                 6
% 3.80/0.96  fd_pseudo_cond                          2
% 3.80/0.96  AC symbols                              0
% 3.80/0.96  
% 3.80/0.96  ------ Schedule dynamic 5 is on 
% 3.80/0.96  
% 3.80/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.80/0.96  
% 3.80/0.96  
% 3.80/0.96  ------ 
% 3.80/0.96  Current options:
% 3.80/0.96  ------ 
% 3.80/0.96  
% 3.80/0.96  ------ Input Options
% 3.80/0.96  
% 3.80/0.96  --out_options                           all
% 3.80/0.96  --tptp_safe_out                         true
% 3.80/0.96  --problem_path                          ""
% 3.80/0.96  --include_path                          ""
% 3.80/0.96  --clausifier                            res/vclausify_rel
% 3.80/0.96  --clausifier_options                    ""
% 3.80/0.96  --stdin                                 false
% 3.80/0.96  --stats_out                             all
% 3.80/0.96  
% 3.80/0.96  ------ General Options
% 3.80/0.96  
% 3.80/0.96  --fof                                   false
% 3.80/0.96  --time_out_real                         305.
% 3.80/0.96  --time_out_virtual                      -1.
% 3.80/0.96  --symbol_type_check                     false
% 3.80/0.96  --clausify_out                          false
% 3.80/0.96  --sig_cnt_out                           false
% 3.80/0.96  --trig_cnt_out                          false
% 3.80/0.96  --trig_cnt_out_tolerance                1.
% 3.80/0.96  --trig_cnt_out_sk_spl                   false
% 3.80/0.96  --abstr_cl_out                          false
% 3.80/0.96  
% 3.80/0.96  ------ Global Options
% 3.80/0.96  
% 3.80/0.96  --schedule                              default
% 3.80/0.96  --add_important_lit                     false
% 3.80/0.96  --prop_solver_per_cl                    1000
% 3.80/0.96  --min_unsat_core                        false
% 3.80/0.96  --soft_assumptions                      false
% 3.80/0.96  --soft_lemma_size                       3
% 3.80/0.96  --prop_impl_unit_size                   0
% 3.80/0.96  --prop_impl_unit                        []
% 3.80/0.96  --share_sel_clauses                     true
% 3.80/0.96  --reset_solvers                         false
% 3.80/0.96  --bc_imp_inh                            [conj_cone]
% 3.80/0.96  --conj_cone_tolerance                   3.
% 3.80/0.96  --extra_neg_conj                        none
% 3.80/0.96  --large_theory_mode                     true
% 3.80/0.96  --prolific_symb_bound                   200
% 3.80/0.96  --lt_threshold                          2000
% 3.80/0.96  --clause_weak_htbl                      true
% 3.80/0.96  --gc_record_bc_elim                     false
% 3.80/0.96  
% 3.80/0.96  ------ Preprocessing Options
% 3.80/0.96  
% 3.80/0.96  --preprocessing_flag                    true
% 3.80/0.96  --time_out_prep_mult                    0.1
% 3.80/0.96  --splitting_mode                        input
% 3.80/0.96  --splitting_grd                         true
% 3.80/0.96  --splitting_cvd                         false
% 3.80/0.96  --splitting_cvd_svl                     false
% 3.80/0.96  --splitting_nvd                         32
% 3.80/0.96  --sub_typing                            true
% 3.80/0.96  --prep_gs_sim                           true
% 3.80/0.96  --prep_unflatten                        true
% 3.80/0.96  --prep_res_sim                          true
% 3.80/0.96  --prep_upred                            true
% 3.80/0.96  --prep_sem_filter                       exhaustive
% 3.80/0.96  --prep_sem_filter_out                   false
% 3.80/0.96  --pred_elim                             true
% 3.80/0.96  --res_sim_input                         true
% 3.80/0.96  --eq_ax_congr_red                       true
% 3.80/0.96  --pure_diseq_elim                       true
% 3.80/0.96  --brand_transform                       false
% 3.80/0.96  --non_eq_to_eq                          false
% 3.80/0.96  --prep_def_merge                        true
% 3.80/0.96  --prep_def_merge_prop_impl              false
% 3.80/0.96  --prep_def_merge_mbd                    true
% 3.80/0.96  --prep_def_merge_tr_red                 false
% 3.80/0.96  --prep_def_merge_tr_cl                  false
% 3.80/0.96  --smt_preprocessing                     true
% 3.80/0.96  --smt_ac_axioms                         fast
% 3.80/0.96  --preprocessed_out                      false
% 3.80/0.96  --preprocessed_stats                    false
% 3.80/0.96  
% 3.80/0.96  ------ Abstraction refinement Options
% 3.80/0.96  
% 3.80/0.96  --abstr_ref                             []
% 3.80/0.96  --abstr_ref_prep                        false
% 3.80/0.96  --abstr_ref_until_sat                   false
% 3.80/0.96  --abstr_ref_sig_restrict                funpre
% 3.80/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/0.96  --abstr_ref_under                       []
% 3.80/0.96  
% 3.80/0.96  ------ SAT Options
% 3.80/0.96  
% 3.80/0.96  --sat_mode                              false
% 3.80/0.96  --sat_fm_restart_options                ""
% 3.80/0.96  --sat_gr_def                            false
% 3.80/0.96  --sat_epr_types                         true
% 3.80/0.96  --sat_non_cyclic_types                  false
% 3.80/0.96  --sat_finite_models                     false
% 3.80/0.96  --sat_fm_lemmas                         false
% 3.80/0.96  --sat_fm_prep                           false
% 3.80/0.96  --sat_fm_uc_incr                        true
% 3.80/0.96  --sat_out_model                         small
% 3.80/0.96  --sat_out_clauses                       false
% 3.80/0.96  
% 3.80/0.96  ------ QBF Options
% 3.80/0.96  
% 3.80/0.96  --qbf_mode                              false
% 3.80/0.96  --qbf_elim_univ                         false
% 3.80/0.96  --qbf_dom_inst                          none
% 3.80/0.96  --qbf_dom_pre_inst                      false
% 3.80/0.96  --qbf_sk_in                             false
% 3.80/0.96  --qbf_pred_elim                         true
% 3.80/0.96  --qbf_split                             512
% 3.80/0.96  
% 3.80/0.96  ------ BMC1 Options
% 3.80/0.96  
% 3.80/0.96  --bmc1_incremental                      false
% 3.80/0.96  --bmc1_axioms                           reachable_all
% 3.80/0.96  --bmc1_min_bound                        0
% 3.80/0.96  --bmc1_max_bound                        -1
% 3.80/0.96  --bmc1_max_bound_default                -1
% 3.80/0.96  --bmc1_symbol_reachability              true
% 3.80/0.96  --bmc1_property_lemmas                  false
% 3.80/0.96  --bmc1_k_induction                      false
% 3.80/0.96  --bmc1_non_equiv_states                 false
% 3.80/0.96  --bmc1_deadlock                         false
% 3.80/0.96  --bmc1_ucm                              false
% 3.80/0.96  --bmc1_add_unsat_core                   none
% 3.80/0.96  --bmc1_unsat_core_children              false
% 3.80/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/0.96  --bmc1_out_stat                         full
% 3.80/0.96  --bmc1_ground_init                      false
% 3.80/0.96  --bmc1_pre_inst_next_state              false
% 3.80/0.96  --bmc1_pre_inst_state                   false
% 3.80/0.96  --bmc1_pre_inst_reach_state             false
% 3.80/0.96  --bmc1_out_unsat_core                   false
% 3.80/0.96  --bmc1_aig_witness_out                  false
% 3.80/0.96  --bmc1_verbose                          false
% 3.80/0.96  --bmc1_dump_clauses_tptp                false
% 3.80/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.80/0.96  --bmc1_dump_file                        -
% 3.80/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.80/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.80/0.96  --bmc1_ucm_extend_mode                  1
% 3.80/0.96  --bmc1_ucm_init_mode                    2
% 3.80/0.96  --bmc1_ucm_cone_mode                    none
% 3.80/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.80/0.96  --bmc1_ucm_relax_model                  4
% 3.80/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.80/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/0.96  --bmc1_ucm_layered_model                none
% 3.80/0.96  --bmc1_ucm_max_lemma_size               10
% 3.80/0.96  
% 3.80/0.96  ------ AIG Options
% 3.80/0.96  
% 3.80/0.96  --aig_mode                              false
% 3.80/0.96  
% 3.80/0.96  ------ Instantiation Options
% 3.80/0.96  
% 3.80/0.96  --instantiation_flag                    true
% 3.80/0.96  --inst_sos_flag                         true
% 3.80/0.96  --inst_sos_phase                        true
% 3.80/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/0.96  --inst_lit_sel_side                     none
% 3.80/0.96  --inst_solver_per_active                1400
% 3.80/0.96  --inst_solver_calls_frac                1.
% 3.80/0.96  --inst_passive_queue_type               priority_queues
% 3.80/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/0.96  --inst_passive_queues_freq              [25;2]
% 3.80/0.96  --inst_dismatching                      true
% 3.80/0.96  --inst_eager_unprocessed_to_passive     true
% 3.80/0.96  --inst_prop_sim_given                   true
% 3.80/0.96  --inst_prop_sim_new                     false
% 3.80/0.96  --inst_subs_new                         false
% 3.80/0.96  --inst_eq_res_simp                      false
% 3.80/0.96  --inst_subs_given                       false
% 3.80/0.96  --inst_orphan_elimination               true
% 3.80/0.96  --inst_learning_loop_flag               true
% 3.80/0.96  --inst_learning_start                   3000
% 3.80/0.96  --inst_learning_factor                  2
% 3.80/0.96  --inst_start_prop_sim_after_learn       3
% 3.80/0.96  --inst_sel_renew                        solver
% 3.80/0.96  --inst_lit_activity_flag                true
% 3.80/0.96  --inst_restr_to_given                   false
% 3.80/0.96  --inst_activity_threshold               500
% 3.80/0.96  --inst_out_proof                        true
% 3.80/0.96  
% 3.80/0.96  ------ Resolution Options
% 3.80/0.96  
% 3.80/0.96  --resolution_flag                       false
% 3.80/0.96  --res_lit_sel                           adaptive
% 3.80/0.96  --res_lit_sel_side                      none
% 3.80/0.96  --res_ordering                          kbo
% 3.80/0.96  --res_to_prop_solver                    active
% 3.80/0.96  --res_prop_simpl_new                    false
% 3.80/0.96  --res_prop_simpl_given                  true
% 3.80/0.96  --res_passive_queue_type                priority_queues
% 3.80/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/0.96  --res_passive_queues_freq               [15;5]
% 3.80/0.96  --res_forward_subs                      full
% 3.80/0.96  --res_backward_subs                     full
% 3.80/0.96  --res_forward_subs_resolution           true
% 3.80/0.96  --res_backward_subs_resolution          true
% 3.80/0.96  --res_orphan_elimination                true
% 3.80/0.96  --res_time_limit                        2.
% 3.80/0.96  --res_out_proof                         true
% 3.80/0.96  
% 3.80/0.96  ------ Superposition Options
% 3.80/0.96  
% 3.80/0.96  --superposition_flag                    true
% 3.80/0.96  --sup_passive_queue_type                priority_queues
% 3.80/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.80/0.96  --demod_completeness_check              fast
% 3.80/0.96  --demod_use_ground                      true
% 3.80/0.96  --sup_to_prop_solver                    passive
% 3.80/0.96  --sup_prop_simpl_new                    true
% 3.80/0.96  --sup_prop_simpl_given                  true
% 3.80/0.96  --sup_fun_splitting                     true
% 3.80/0.96  --sup_smt_interval                      50000
% 3.80/0.96  
% 3.80/0.96  ------ Superposition Simplification Setup
% 3.80/0.96  
% 3.80/0.96  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.80/0.96  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.80/0.96  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.80/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.80/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.80/0.96  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.80/0.96  --sup_immed_triv                        [TrivRules]
% 3.80/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.96  --sup_immed_bw_main                     []
% 3.80/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.80/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.96  --sup_input_bw                          []
% 3.80/0.96  
% 3.80/0.96  ------ Combination Options
% 3.80/0.96  
% 3.80/0.96  --comb_res_mult                         3
% 3.80/0.96  --comb_sup_mult                         2
% 3.80/0.96  --comb_inst_mult                        10
% 3.80/0.96  
% 3.80/0.96  ------ Debug Options
% 3.80/0.96  
% 3.80/0.96  --dbg_backtrace                         false
% 3.80/0.96  --dbg_dump_prop_clauses                 false
% 3.80/0.96  --dbg_dump_prop_clauses_file            -
% 3.80/0.96  --dbg_out_stat                          false
% 3.80/0.96  
% 3.80/0.96  
% 3.80/0.96  
% 3.80/0.96  
% 3.80/0.96  ------ Proving...
% 3.80/0.96  
% 3.80/0.96  
% 3.80/0.96  % SZS status Theorem for theBenchmark.p
% 3.80/0.96  
% 3.80/0.96   Resolution empty clause
% 3.80/0.96  
% 3.80/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.80/0.96  
% 3.80/0.96  fof(f2,axiom,(
% 3.80/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f55,plain,(
% 3.80/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.80/0.96    inference(nnf_transformation,[],[f2])).
% 3.80/0.96  
% 3.80/0.96  fof(f56,plain,(
% 3.80/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.80/0.96    inference(flattening,[],[f55])).
% 3.80/0.96  
% 3.80/0.96  fof(f74,plain,(
% 3.80/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.80/0.96    inference(cnf_transformation,[],[f56])).
% 3.80/0.96  
% 3.80/0.96  fof(f132,plain,(
% 3.80/0.96    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.80/0.96    inference(equality_resolution,[],[f74])).
% 3.80/0.96  
% 3.80/0.96  fof(f118,plain,(
% 3.80/0.96    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.80/0.96    inference(cnf_transformation,[],[f72])).
% 3.80/0.96  
% 3.80/0.96  fof(f24,conjecture,(
% 3.80/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f25,negated_conjecture,(
% 3.80/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.80/0.96    inference(negated_conjecture,[],[f24])).
% 3.80/0.96  
% 3.80/0.96  fof(f53,plain,(
% 3.80/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.80/0.96    inference(ennf_transformation,[],[f25])).
% 3.80/0.96  
% 3.80/0.96  fof(f54,plain,(
% 3.80/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.80/0.96    inference(flattening,[],[f53])).
% 3.80/0.96  
% 3.80/0.96  fof(f66,plain,(
% 3.80/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.80/0.96    inference(nnf_transformation,[],[f54])).
% 3.80/0.96  
% 3.80/0.96  fof(f67,plain,(
% 3.80/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.80/0.96    inference(flattening,[],[f66])).
% 3.80/0.96  
% 3.80/0.96  fof(f71,plain,(
% 3.80/0.96    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK5 = X2 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK5))) )),
% 3.80/0.96    introduced(choice_axiom,[])).
% 3.80/0.96  
% 3.80/0.96  fof(f70,plain,(
% 3.80/0.96    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK4,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK4,X0,X1)) & sK4 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.80/0.96    introduced(choice_axiom,[])).
% 3.80/0.96  
% 3.80/0.96  fof(f69,plain,(
% 3.80/0.96    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(X2,X0,sK3)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(X2,X0,sK3)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))) )),
% 3.80/0.96    introduced(choice_axiom,[])).
% 3.80/0.96  
% 3.80/0.96  fof(f68,plain,(
% 3.80/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK2,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK2,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 3.80/0.96    introduced(choice_axiom,[])).
% 3.80/0.96  
% 3.80/0.96  fof(f72,plain,(
% 3.80/0.96    ((((~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK4,sK2,sK3)) & (v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK4,sK2,sK3)) & sK4 = sK5 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 3.80/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f67,f71,f70,f69,f68])).
% 3.80/0.96  
% 3.80/0.96  fof(f122,plain,(
% 3.80/0.96    sK4 = sK5),
% 3.80/0.96    inference(cnf_transformation,[],[f72])).
% 3.80/0.96  
% 3.80/0.96  fof(f128,plain,(
% 3.80/0.96    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.80/0.96    inference(definition_unfolding,[],[f118,f122])).
% 3.80/0.96  
% 3.80/0.96  fof(f10,axiom,(
% 3.80/0.96    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f36,plain,(
% 3.80/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.80/0.96    inference(ennf_transformation,[],[f10])).
% 3.80/0.96  
% 3.80/0.96  fof(f37,plain,(
% 3.80/0.96    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.80/0.96    inference(flattening,[],[f36])).
% 3.80/0.96  
% 3.80/0.96  fof(f86,plain,(
% 3.80/0.96    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 3.80/0.96    inference(cnf_transformation,[],[f37])).
% 3.80/0.96  
% 3.80/0.96  fof(f13,axiom,(
% 3.80/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f39,plain,(
% 3.80/0.96    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.80/0.96    inference(ennf_transformation,[],[f13])).
% 3.80/0.96  
% 3.80/0.96  fof(f40,plain,(
% 3.80/0.96    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.80/0.96    inference(flattening,[],[f39])).
% 3.80/0.96  
% 3.80/0.96  fof(f92,plain,(
% 3.80/0.96    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.80/0.96    inference(cnf_transformation,[],[f40])).
% 3.80/0.96  
% 3.80/0.96  fof(f116,plain,(
% 3.80/0.96    v1_funct_1(sK4)),
% 3.80/0.96    inference(cnf_transformation,[],[f72])).
% 3.80/0.96  
% 3.80/0.96  fof(f130,plain,(
% 3.80/0.96    v1_funct_1(sK5)),
% 3.80/0.96    inference(definition_unfolding,[],[f116,f122])).
% 3.80/0.96  
% 3.80/0.96  fof(f121,plain,(
% 3.80/0.96    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))),
% 3.80/0.96    inference(cnf_transformation,[],[f72])).
% 3.80/0.96  
% 3.80/0.96  fof(f18,axiom,(
% 3.80/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f43,plain,(
% 3.80/0.96    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.80/0.96    inference(ennf_transformation,[],[f18])).
% 3.80/0.96  
% 3.80/0.96  fof(f44,plain,(
% 3.80/0.96    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.80/0.96    inference(flattening,[],[f43])).
% 3.80/0.96  
% 3.80/0.96  fof(f103,plain,(
% 3.80/0.96    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f44])).
% 3.80/0.96  
% 3.80/0.96  fof(f120,plain,(
% 3.80/0.96    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))),
% 3.80/0.96    inference(cnf_transformation,[],[f72])).
% 3.80/0.96  
% 3.80/0.96  fof(f14,axiom,(
% 3.80/0.96    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f41,plain,(
% 3.80/0.96    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.80/0.96    inference(ennf_transformation,[],[f14])).
% 3.80/0.96  
% 3.80/0.96  fof(f42,plain,(
% 3.80/0.96    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.80/0.96    inference(flattening,[],[f41])).
% 3.80/0.96  
% 3.80/0.96  fof(f61,plain,(
% 3.80/0.96    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.80/0.96    inference(nnf_transformation,[],[f42])).
% 3.80/0.96  
% 3.80/0.96  fof(f93,plain,(
% 3.80/0.96    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f61])).
% 3.80/0.96  
% 3.80/0.96  fof(f8,axiom,(
% 3.80/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f34,plain,(
% 3.80/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.80/0.96    inference(ennf_transformation,[],[f8])).
% 3.80/0.96  
% 3.80/0.96  fof(f84,plain,(
% 3.80/0.96    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.80/0.96    inference(cnf_transformation,[],[f34])).
% 3.80/0.96  
% 3.80/0.96  fof(f9,axiom,(
% 3.80/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f28,plain,(
% 3.80/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.80/0.96    inference(pure_predicate_removal,[],[f9])).
% 3.80/0.96  
% 3.80/0.96  fof(f35,plain,(
% 3.80/0.96    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.80/0.96    inference(ennf_transformation,[],[f28])).
% 3.80/0.96  
% 3.80/0.96  fof(f85,plain,(
% 3.80/0.96    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.80/0.96    inference(cnf_transformation,[],[f35])).
% 3.80/0.96  
% 3.80/0.96  fof(f117,plain,(
% 3.80/0.96    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.80/0.96    inference(cnf_transformation,[],[f72])).
% 3.80/0.96  
% 3.80/0.96  fof(f129,plain,(
% 3.80/0.96    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.80/0.96    inference(definition_unfolding,[],[f117,f122])).
% 3.80/0.96  
% 3.80/0.96  fof(f23,axiom,(
% 3.80/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f51,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.80/0.96    inference(ennf_transformation,[],[f23])).
% 3.80/0.96  
% 3.80/0.96  fof(f52,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.80/0.96    inference(flattening,[],[f51])).
% 3.80/0.96  
% 3.80/0.96  fof(f65,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.80/0.96    inference(nnf_transformation,[],[f52])).
% 3.80/0.96  
% 3.80/0.96  fof(f110,plain,(
% 3.80/0.96    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f65])).
% 3.80/0.96  
% 3.80/0.96  fof(f140,plain,(
% 3.80/0.96    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.80/0.96    inference(equality_resolution,[],[f110])).
% 3.80/0.96  
% 3.80/0.96  fof(f112,plain,(
% 3.80/0.96    v2_pre_topc(sK2)),
% 3.80/0.96    inference(cnf_transformation,[],[f72])).
% 3.80/0.96  
% 3.80/0.96  fof(f113,plain,(
% 3.80/0.96    l1_pre_topc(sK2)),
% 3.80/0.96    inference(cnf_transformation,[],[f72])).
% 3.80/0.96  
% 3.80/0.96  fof(f114,plain,(
% 3.80/0.96    v2_pre_topc(sK3)),
% 3.80/0.96    inference(cnf_transformation,[],[f72])).
% 3.80/0.96  
% 3.80/0.96  fof(f115,plain,(
% 3.80/0.96    l1_pre_topc(sK3)),
% 3.80/0.96    inference(cnf_transformation,[],[f72])).
% 3.80/0.96  
% 3.80/0.96  fof(f123,plain,(
% 3.80/0.96    v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK4,sK2,sK3)),
% 3.80/0.96    inference(cnf_transformation,[],[f72])).
% 3.80/0.96  
% 3.80/0.96  fof(f127,plain,(
% 3.80/0.96    v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK5,sK2,sK3)),
% 3.80/0.96    inference(definition_unfolding,[],[f123,f122])).
% 3.80/0.96  
% 3.80/0.96  fof(f124,plain,(
% 3.80/0.96    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK4,sK2,sK3)),
% 3.80/0.96    inference(cnf_transformation,[],[f72])).
% 3.80/0.96  
% 3.80/0.96  fof(f126,plain,(
% 3.80/0.96    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK5,sK2,sK3)),
% 3.80/0.96    inference(definition_unfolding,[],[f124,f122])).
% 3.80/0.96  
% 3.80/0.96  fof(f22,axiom,(
% 3.80/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f49,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.80/0.96    inference(ennf_transformation,[],[f22])).
% 3.80/0.96  
% 3.80/0.96  fof(f50,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.80/0.96    inference(flattening,[],[f49])).
% 3.80/0.96  
% 3.80/0.96  fof(f64,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.80/0.96    inference(nnf_transformation,[],[f50])).
% 3.80/0.96  
% 3.80/0.96  fof(f109,plain,(
% 3.80/0.96    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f64])).
% 3.80/0.96  
% 3.80/0.96  fof(f137,plain,(
% 3.80/0.96    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.80/0.96    inference(equality_resolution,[],[f109])).
% 3.80/0.96  
% 3.80/0.96  fof(f111,plain,(
% 3.80/0.96    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f65])).
% 3.80/0.96  
% 3.80/0.96  fof(f139,plain,(
% 3.80/0.96    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.80/0.96    inference(equality_resolution,[],[f111])).
% 3.80/0.96  
% 3.80/0.96  fof(f108,plain,(
% 3.80/0.96    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f64])).
% 3.80/0.96  
% 3.80/0.96  fof(f138,plain,(
% 3.80/0.96    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.80/0.96    inference(equality_resolution,[],[f108])).
% 3.80/0.96  
% 3.80/0.96  fof(f21,axiom,(
% 3.80/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f26,plain,(
% 3.80/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 3.80/0.96    inference(pure_predicate_removal,[],[f21])).
% 3.80/0.96  
% 3.80/0.96  fof(f47,plain,(
% 3.80/0.96    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.80/0.96    inference(ennf_transformation,[],[f26])).
% 3.80/0.96  
% 3.80/0.96  fof(f48,plain,(
% 3.80/0.96    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.80/0.96    inference(flattening,[],[f47])).
% 3.80/0.96  
% 3.80/0.96  fof(f107,plain,(
% 3.80/0.96    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f48])).
% 3.80/0.96  
% 3.80/0.96  fof(f19,axiom,(
% 3.80/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f27,plain,(
% 3.80/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 3.80/0.96    inference(pure_predicate_removal,[],[f19])).
% 3.80/0.96  
% 3.80/0.96  fof(f45,plain,(
% 3.80/0.96    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.80/0.96    inference(ennf_transformation,[],[f27])).
% 3.80/0.96  
% 3.80/0.96  fof(f105,plain,(
% 3.80/0.96    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.80/0.96    inference(cnf_transformation,[],[f45])).
% 3.80/0.96  
% 3.80/0.96  fof(f20,axiom,(
% 3.80/0.96    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f46,plain,(
% 3.80/0.96    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.80/0.96    inference(ennf_transformation,[],[f20])).
% 3.80/0.96  
% 3.80/0.96  fof(f106,plain,(
% 3.80/0.96    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f46])).
% 3.80/0.96  
% 3.80/0.96  fof(f3,axiom,(
% 3.80/0.96    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f57,plain,(
% 3.80/0.96    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.80/0.96    inference(nnf_transformation,[],[f3])).
% 3.80/0.96  
% 3.80/0.96  fof(f58,plain,(
% 3.80/0.96    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.80/0.96    inference(flattening,[],[f57])).
% 3.80/0.96  
% 3.80/0.96  fof(f79,plain,(
% 3.80/0.96    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.80/0.96    inference(cnf_transformation,[],[f58])).
% 3.80/0.96  
% 3.80/0.96  fof(f133,plain,(
% 3.80/0.96    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.80/0.96    inference(equality_resolution,[],[f79])).
% 3.80/0.96  
% 3.80/0.96  fof(f94,plain,(
% 3.80/0.96    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f61])).
% 3.80/0.96  
% 3.80/0.96  fof(f135,plain,(
% 3.80/0.96    ( ! [X1] : (v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.80/0.96    inference(equality_resolution,[],[f94])).
% 3.80/0.96  
% 3.80/0.96  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f132]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_3956,plain,
% 3.80/0.96      ( r1_tarski(X0,X0) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_43,negated_conjecture,
% 3.80/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.80/0.96      inference(cnf_transformation,[],[f128]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_3927,plain,
% 3.80/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_13,plain,
% 3.80/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.80/0.96      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 3.80/0.96      inference(cnf_transformation,[],[f86]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_3952,plain,
% 3.80/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.80/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 3.80/0.96      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_6751,plain,
% 3.80/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK3)))) = iProver_top
% 3.80/0.96      | r1_tarski(k1_relat_1(sK5),X0) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_3927,c_3952]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_18,plain,
% 3.80/0.96      ( v1_funct_2(X0,X1,X2)
% 3.80/0.96      | ~ v1_partfun1(X0,X1)
% 3.80/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.96      | ~ v1_funct_1(X0) ),
% 3.80/0.96      inference(cnf_transformation,[],[f92]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_3950,plain,
% 3.80/0.96      ( v1_funct_2(X0,X1,X2) = iProver_top
% 3.80/0.96      | v1_partfun1(X0,X1) != iProver_top
% 3.80/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.80/0.96      | v1_funct_1(X0) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_7435,plain,
% 3.80/0.96      ( v1_funct_2(sK5,X0,u1_struct_0(sK3)) = iProver_top
% 3.80/0.96      | v1_partfun1(sK5,X0) != iProver_top
% 3.80/0.96      | r1_tarski(k1_relat_1(sK5),X0) != iProver_top
% 3.80/0.96      | v1_funct_1(sK5) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_6751,c_3950]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_45,negated_conjecture,
% 3.80/0.96      ( v1_funct_1(sK5) ),
% 3.80/0.96      inference(cnf_transformation,[],[f130]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_54,plain,
% 3.80/0.96      ( v1_funct_1(sK5) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_7618,plain,
% 3.80/0.96      ( r1_tarski(k1_relat_1(sK5),X0) != iProver_top
% 3.80/0.96      | v1_partfun1(sK5,X0) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,X0,u1_struct_0(sK3)) = iProver_top ),
% 3.80/0.96      inference(global_propositional_subsumption,[status(thm)],[c_7435,c_54]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_7619,plain,
% 3.80/0.96      ( v1_funct_2(sK5,X0,u1_struct_0(sK3)) = iProver_top
% 3.80/0.96      | v1_partfun1(sK5,X0) != iProver_top
% 3.80/0.96      | r1_tarski(k1_relat_1(sK5),X0) != iProver_top ),
% 3.80/0.96      inference(renaming,[status(thm)],[c_7618]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_40,negated_conjecture,
% 3.80/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
% 3.80/0.96      inference(cnf_transformation,[],[f121]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_3930,plain,
% 3.80/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_30,plain,
% 3.80/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 3.80/0.96      | v1_partfun1(X0,X1)
% 3.80/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.80/0.96      | ~ v1_funct_1(X0)
% 3.80/0.96      | k1_xboole_0 = X2 ),
% 3.80/0.96      inference(cnf_transformation,[],[f103]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_3940,plain,
% 3.80/0.96      ( k1_xboole_0 = X0
% 3.80/0.96      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.80/0.96      | v1_partfun1(X1,X2) = iProver_top
% 3.80/0.96      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.80/0.96      | v1_funct_1(X1) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8145,plain,
% 3.80/0.96      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.80/0.96      | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top
% 3.80/0.96      | v1_funct_1(sK5) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_3930,c_3940]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_41,negated_conjecture,
% 3.80/0.96      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
% 3.80/0.96      inference(cnf_transformation,[],[f120]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_58,plain,
% 3.80/0.96      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8402,plain,
% 3.80/0.96      ( v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top
% 3.80/0.96      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0 ),
% 3.80/0.96      inference(global_propositional_subsumption,
% 3.80/0.96                [status(thm)],
% 3.80/0.96                [c_8145,c_54,c_58]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8403,plain,
% 3.80/0.96      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 3.80/0.96      | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
% 3.80/0.96      inference(renaming,[status(thm)],[c_8402]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_21,plain,
% 3.80/0.96      ( ~ v1_partfun1(X0,X1)
% 3.80/0.96      | ~ v4_relat_1(X0,X1)
% 3.80/0.96      | ~ v1_relat_1(X0)
% 3.80/0.96      | k1_relat_1(X0) = X1 ),
% 3.80/0.96      inference(cnf_transformation,[],[f93]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_3948,plain,
% 3.80/0.96      ( k1_relat_1(X0) = X1
% 3.80/0.96      | v1_partfun1(X0,X1) != iProver_top
% 3.80/0.96      | v4_relat_1(X0,X1) != iProver_top
% 3.80/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8406,plain,
% 3.80/0.96      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 3.80/0.96      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 3.80/0.96      | v4_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 3.80/0.96      | v1_relat_1(sK5) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_8403,c_3948]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_59,plain,
% 3.80/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_11,plain,
% 3.80/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.80/0.96      inference(cnf_transformation,[],[f84]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4972,plain,
% 3.80/0.96      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 3.80/0.96      | v1_relat_1(sK5) ),
% 3.80/0.96      inference(instantiation,[status(thm)],[c_11]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4973,plain,
% 3.80/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.80/0.96      | v1_relat_1(sK5) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_4972]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_12,plain,
% 3.80/0.96      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.80/0.96      inference(cnf_transformation,[],[f85]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_3953,plain,
% 3.80/0.96      ( v4_relat_1(X0,X1) = iProver_top
% 3.80/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_6371,plain,
% 3.80/0.96      ( v4_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_3930,c_3953]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_9274,plain,
% 3.80/0.96      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 3.80/0.96      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 3.80/0.96      inference(global_propositional_subsumption,
% 3.80/0.96                [status(thm)],
% 3.80/0.96                [c_8406,c_59,c_4973,c_6371]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_3929,plain,
% 3.80/0.96      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_9312,plain,
% 3.80/0.96      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_9274,c_3929]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8146,plain,
% 3.80/0.96      ( u1_struct_0(sK3) = k1_xboole_0
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | v1_partfun1(sK5,u1_struct_0(sK2)) = iProver_top
% 3.80/0.96      | v1_funct_1(sK5) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_3927,c_3940]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_44,negated_conjecture,
% 3.80/0.96      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.80/0.96      inference(cnf_transformation,[],[f129]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_55,plain,
% 3.80/0.96      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8335,plain,
% 3.80/0.96      ( v1_partfun1(sK5,u1_struct_0(sK2)) = iProver_top
% 3.80/0.96      | u1_struct_0(sK3) = k1_xboole_0 ),
% 3.80/0.96      inference(global_propositional_subsumption,
% 3.80/0.96                [status(thm)],
% 3.80/0.96                [c_8146,c_54,c_55]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8336,plain,
% 3.80/0.96      ( u1_struct_0(sK3) = k1_xboole_0
% 3.80/0.96      | v1_partfun1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.80/0.96      inference(renaming,[status(thm)],[c_8335]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8339,plain,
% 3.80/0.96      ( u1_struct_0(sK3) = k1_xboole_0
% 3.80/0.96      | u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.80/0.96      | v4_relat_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.80/0.96      | v1_relat_1(sK5) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_8336,c_3948]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_6372,plain,
% 3.80/0.96      ( v4_relat_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_3927,c_3953]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8460,plain,
% 3.80/0.96      ( u1_struct_0(sK3) = k1_xboole_0 | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 3.80/0.96      inference(global_propositional_subsumption,
% 3.80/0.96                [status(thm)],
% 3.80/0.96                [c_8339,c_59,c_4973,c_6372]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_37,plain,
% 3.80/0.96      ( ~ v5_pre_topc(X0,X1,X2)
% 3.80/0.96      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 3.80/0.96      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.80/0.96      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 3.80/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.80/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 3.80/0.96      | ~ v2_pre_topc(X1)
% 3.80/0.96      | ~ v2_pre_topc(X2)
% 3.80/0.96      | ~ l1_pre_topc(X1)
% 3.80/0.96      | ~ l1_pre_topc(X2)
% 3.80/0.96      | ~ v1_funct_1(X0) ),
% 3.80/0.96      inference(cnf_transformation,[],[f140]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_3933,plain,
% 3.80/0.96      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.80/0.96      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 3.80/0.96      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.80/0.96      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 3.80/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.80/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 3.80/0.96      | v2_pre_topc(X1) != iProver_top
% 3.80/0.96      | v2_pre_topc(X2) != iProver_top
% 3.80/0.96      | l1_pre_topc(X1) != iProver_top
% 3.80/0.96      | l1_pre_topc(X2) != iProver_top
% 3.80/0.96      | v1_funct_1(X0) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_5273,plain,
% 3.80/0.96      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.80/0.96      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.80/0.96      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.80/0.96      | v2_pre_topc(sK3) != iProver_top
% 3.80/0.96      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.80/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.80/0.96      | v1_funct_1(sK5) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_3930,c_3933]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_49,negated_conjecture,
% 3.80/0.96      ( v2_pre_topc(sK2) ),
% 3.80/0.96      inference(cnf_transformation,[],[f112]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_50,plain,
% 3.80/0.96      ( v2_pre_topc(sK2) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_48,negated_conjecture,
% 3.80/0.96      ( l1_pre_topc(sK2) ),
% 3.80/0.96      inference(cnf_transformation,[],[f113]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_51,plain,
% 3.80/0.96      ( l1_pre_topc(sK2) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_47,negated_conjecture,
% 3.80/0.96      ( v2_pre_topc(sK3) ),
% 3.80/0.96      inference(cnf_transformation,[],[f114]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_52,plain,
% 3.80/0.96      ( v2_pre_topc(sK3) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_46,negated_conjecture,
% 3.80/0.96      ( l1_pre_topc(sK3) ),
% 3.80/0.96      inference(cnf_transformation,[],[f115]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_53,plain,
% 3.80/0.96      ( l1_pre_topc(sK3) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_56,plain,
% 3.80/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_39,negated_conjecture,
% 3.80/0.96      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.80/0.96      | v5_pre_topc(sK5,sK2,sK3) ),
% 3.80/0.96      inference(cnf_transformation,[],[f127]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_60,plain,
% 3.80/0.96      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.80/0.96      | v5_pre_topc(sK5,sK2,sK3) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_38,negated_conjecture,
% 3.80/0.96      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.80/0.96      | ~ v5_pre_topc(sK5,sK2,sK3) ),
% 3.80/0.96      inference(cnf_transformation,[],[f126]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_61,plain,
% 3.80/0.96      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.96      | v5_pre_topc(sK5,sK2,sK3) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_34,plain,
% 3.80/0.96      ( v5_pre_topc(X0,X1,X2)
% 3.80/0.96      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 3.80/0.96      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.80/0.96      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 3.80/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.80/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 3.80/0.96      | ~ v2_pre_topc(X1)
% 3.80/0.96      | ~ v2_pre_topc(X2)
% 3.80/0.96      | ~ l1_pre_topc(X1)
% 3.80/0.96      | ~ l1_pre_topc(X2)
% 3.80/0.96      | ~ v1_funct_1(X0) ),
% 3.80/0.96      inference(cnf_transformation,[],[f137]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4009,plain,
% 3.80/0.96      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 3.80/0.96      | v5_pre_topc(sK5,sK2,sK3)
% 3.80/0.96      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 3.80/0.96      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.80/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 3.80/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.80/0.96      | ~ v2_pre_topc(sK3)
% 3.80/0.96      | ~ v2_pre_topc(sK2)
% 3.80/0.96      | ~ l1_pre_topc(sK3)
% 3.80/0.96      | ~ l1_pre_topc(sK2)
% 3.80/0.96      | ~ v1_funct_1(sK5) ),
% 3.80/0.96      inference(instantiation,[status(thm)],[c_34]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4013,plain,
% 3.80/0.96      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 3.80/0.96      | v5_pre_topc(sK5,sK2,sK3) = iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.80/0.96      | v2_pre_topc(sK3) != iProver_top
% 3.80/0.96      | v2_pre_topc(sK2) != iProver_top
% 3.80/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.80/0.96      | l1_pre_topc(sK2) != iProver_top
% 3.80/0.96      | v1_funct_1(sK5) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_4009]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_36,plain,
% 3.80/0.96      ( v5_pre_topc(X0,X1,X2)
% 3.80/0.96      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 3.80/0.96      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.80/0.96      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 3.80/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.80/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 3.80/0.96      | ~ v2_pre_topc(X1)
% 3.80/0.96      | ~ v2_pre_topc(X2)
% 3.80/0.96      | ~ l1_pre_topc(X1)
% 3.80/0.96      | ~ l1_pre_topc(X2)
% 3.80/0.96      | ~ v1_funct_1(X0) ),
% 3.80/0.96      inference(cnf_transformation,[],[f139]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4023,plain,
% 3.80/0.96      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.80/0.96      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 3.80/0.96      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 3.80/0.96      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 3.80/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 3.80/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 3.80/0.96      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.80/0.96      | ~ v2_pre_topc(sK3)
% 3.80/0.96      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.80/0.96      | ~ l1_pre_topc(sK3)
% 3.80/0.96      | ~ v1_funct_1(sK5) ),
% 3.80/0.96      inference(instantiation,[status(thm)],[c_36]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4024,plain,
% 3.80/0.96      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.96      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.80/0.96      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.80/0.96      | v2_pre_topc(sK3) != iProver_top
% 3.80/0.96      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.80/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.80/0.96      | v1_funct_1(sK5) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_4023]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_35,plain,
% 3.80/0.96      ( ~ v5_pre_topc(X0,X1,X2)
% 3.80/0.96      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 3.80/0.96      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.80/0.96      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 3.80/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.80/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 3.80/0.96      | ~ v2_pre_topc(X1)
% 3.80/0.96      | ~ v2_pre_topc(X2)
% 3.80/0.96      | ~ l1_pre_topc(X1)
% 3.80/0.96      | ~ l1_pre_topc(X2)
% 3.80/0.96      | ~ v1_funct_1(X0) ),
% 3.80/0.96      inference(cnf_transformation,[],[f138]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4028,plain,
% 3.80/0.96      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 3.80/0.96      | ~ v5_pre_topc(sK5,sK2,sK3)
% 3.80/0.96      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 3.80/0.96      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.80/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 3.80/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.80/0.96      | ~ v2_pre_topc(sK3)
% 3.80/0.96      | ~ v2_pre_topc(sK2)
% 3.80/0.96      | ~ l1_pre_topc(sK3)
% 3.80/0.96      | ~ l1_pre_topc(sK2)
% 3.80/0.96      | ~ v1_funct_1(sK5) ),
% 3.80/0.96      inference(instantiation,[status(thm)],[c_35]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4029,plain,
% 3.80/0.96      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
% 3.80/0.96      | v5_pre_topc(sK5,sK2,sK3) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.80/0.96      | v2_pre_topc(sK3) != iProver_top
% 3.80/0.96      | v2_pre_topc(sK2) != iProver_top
% 3.80/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.80/0.96      | l1_pre_topc(sK2) != iProver_top
% 3.80/0.96      | v1_funct_1(sK5) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_4028]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_33,plain,
% 3.80/0.96      ( ~ v2_pre_topc(X0)
% 3.80/0.96      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.80/0.96      | ~ l1_pre_topc(X0) ),
% 3.80/0.96      inference(cnf_transformation,[],[f107]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4071,plain,
% 3.80/0.96      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.80/0.96      | ~ v2_pre_topc(sK2)
% 3.80/0.96      | ~ l1_pre_topc(sK2) ),
% 3.80/0.96      inference(instantiation,[status(thm)],[c_33]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4072,plain,
% 3.80/0.96      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.80/0.96      | v2_pre_topc(sK2) != iProver_top
% 3.80/0.96      | l1_pre_topc(sK2) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_4071]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_31,plain,
% 3.80/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.80/0.96      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.80/0.96      inference(cnf_transformation,[],[f105]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4156,plain,
% 3.80/0.96      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.80/0.96      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 3.80/0.96      inference(instantiation,[status(thm)],[c_31]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4157,plain,
% 3.80/0.96      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 3.80/0.96      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_4156]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_32,plain,
% 3.80/0.96      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.80/0.96      | ~ l1_pre_topc(X0) ),
% 3.80/0.96      inference(cnf_transformation,[],[f106]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4216,plain,
% 3.80/0.96      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.80/0.96      | ~ l1_pre_topc(sK2) ),
% 3.80/0.96      inference(instantiation,[status(thm)],[c_32]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4217,plain,
% 3.80/0.96      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 3.80/0.96      | l1_pre_topc(sK2) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_4216]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_5629,plain,
% 3.80/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top ),
% 3.80/0.96      inference(global_propositional_subsumption,
% 3.80/0.96                [status(thm)],
% 3.80/0.96                [c_5273,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,c_60,
% 3.80/0.96                 c_61,c_4013,c_4024,c_4029,c_4072,c_4157,c_4217]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_5630,plain,
% 3.80/0.96      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 3.80/0.96      inference(renaming,[status(thm)],[c_5629]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_5633,plain,
% 3.80/0.96      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 3.80/0.96      inference(global_propositional_subsumption,
% 3.80/0.96                [status(thm)],
% 3.80/0.96                [c_5630,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,c_60,
% 3.80/0.96                 c_4024,c_4029,c_4072,c_4157,c_4217]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8492,plain,
% 3.80/0.96      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0))) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_8460,c_5633]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4,plain,
% 3.80/0.96      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.80/0.96      inference(cnf_transformation,[],[f133]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8503,plain,
% 3.80/0.96      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.80/0.96      inference(demodulation,[status(thm)],[c_8492,c_4]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8499,plain,
% 3.80/0.96      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_8460,c_3927]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8501,plain,
% 3.80/0.96      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.80/0.96      inference(demodulation,[status(thm)],[c_8499,c_4]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8930,plain,
% 3.80/0.96      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 3.80/0.96      inference(global_propositional_subsumption,[status(thm)],[c_8503,c_8501]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8931,plain,
% 3.80/0.96      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 3.80/0.96      inference(renaming,[status(thm)],[c_8930]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8935,plain,
% 3.80/0.96      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_8460,c_8931]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_9806,plain,
% 3.80/0.96      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 3.80/0.96      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_9312,c_8935]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_9899,plain,
% 3.80/0.96      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.80/0.96      | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(sK3)) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_9806,c_8931]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_10444,plain,
% 3.80/0.96      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.80/0.96      | v1_partfun1(sK5,k1_relat_1(sK5)) != iProver_top
% 3.80/0.96      | r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_7619,c_9899]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_6996,plain,
% 3.80/0.96      ( v4_relat_1(sK5,X0) = iProver_top
% 3.80/0.96      | r1_tarski(k1_relat_1(sK5),X0) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_6751,c_3953]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_7174,plain,
% 3.80/0.96      ( v4_relat_1(sK5,k1_relat_1(sK5)) = iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_3956,c_6996]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_20,plain,
% 3.80/0.96      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.80/0.96      | ~ v4_relat_1(X0,k1_relat_1(X0))
% 3.80/0.96      | ~ v1_relat_1(X0) ),
% 3.80/0.96      inference(cnf_transformation,[],[f135]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_3949,plain,
% 3.80/0.96      ( v1_partfun1(X0,k1_relat_1(X0)) = iProver_top
% 3.80/0.96      | v4_relat_1(X0,k1_relat_1(X0)) != iProver_top
% 3.80/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_8257,plain,
% 3.80/0.96      ( v1_partfun1(sK5,k1_relat_1(sK5)) = iProver_top
% 3.80/0.96      | v1_relat_1(sK5) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_7174,c_3949]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_10491,plain,
% 3.80/0.96      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.80/0.96      | r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) != iProver_top ),
% 3.80/0.96      inference(global_propositional_subsumption,
% 3.80/0.96                [status(thm)],
% 3.80/0.96                [c_10444,c_59,c_4973,c_8257]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_10495,plain,
% 3.80/0.96      ( u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_3956,c_10491]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_6750,plain,
% 3.80/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top
% 3.80/0.96      | r1_tarski(k1_relat_1(sK5),X0) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_3930,c_3952]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_3935,plain,
% 3.80/0.96      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.80/0.96      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 3.80/0.96      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.80/0.96      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 3.80/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.80/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 3.80/0.96      | v2_pre_topc(X1) != iProver_top
% 3.80/0.96      | v2_pre_topc(X2) != iProver_top
% 3.80/0.96      | l1_pre_topc(X1) != iProver_top
% 3.80/0.96      | l1_pre_topc(X2) != iProver_top
% 3.80/0.96      | v1_funct_1(X0) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_6647,plain,
% 3.80/0.96      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.80/0.96      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.80/0.96      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.96      | v2_pre_topc(sK2) != iProver_top
% 3.80/0.96      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.96      | l1_pre_topc(sK2) != iProver_top
% 3.80/0.96      | v1_funct_1(sK5) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_3930,c_3935]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4010,plain,
% 3.80/0.96      ( ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.80/0.96      | v5_pre_topc(sK5,sK2,sK3)
% 3.80/0.96      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 3.80/0.96      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.80/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 3.80/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.80/0.96      | ~ v2_pre_topc(sK3)
% 3.80/0.96      | ~ v2_pre_topc(sK2)
% 3.80/0.96      | ~ l1_pre_topc(sK3)
% 3.80/0.96      | ~ l1_pre_topc(sK2)
% 3.80/0.96      | ~ v1_funct_1(sK5) ),
% 3.80/0.96      inference(instantiation,[status(thm)],[c_36]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4011,plain,
% 3.80/0.96      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.96      | v5_pre_topc(sK5,sK2,sK3) = iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.80/0.96      | v2_pre_topc(sK3) != iProver_top
% 3.80/0.96      | v2_pre_topc(sK2) != iProver_top
% 3.80/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.80/0.96      | l1_pre_topc(sK2) != iProver_top
% 3.80/0.96      | v1_funct_1(sK5) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_4010]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4036,plain,
% 3.80/0.96      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.80/0.96      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.80/0.96      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 3.80/0.96      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 3.80/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 3.80/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 3.80/0.96      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.80/0.96      | ~ v2_pre_topc(sK2)
% 3.80/0.96      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.80/0.96      | ~ l1_pre_topc(sK2)
% 3.80/0.96      | ~ v1_funct_1(sK5) ),
% 3.80/0.96      inference(instantiation,[status(thm)],[c_34]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4040,plain,
% 3.80/0.96      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.96      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.80/0.96      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.96      | v2_pre_topc(sK2) != iProver_top
% 3.80/0.96      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.96      | l1_pre_topc(sK2) != iProver_top
% 3.80/0.96      | v1_funct_1(sK5) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_4036]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4042,plain,
% 3.80/0.96      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.80/0.96      | ~ v5_pre_topc(sK5,sK2,sK3)
% 3.80/0.96      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 3.80/0.96      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.80/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 3.80/0.96      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.80/0.96      | ~ v2_pre_topc(sK3)
% 3.80/0.96      | ~ v2_pre_topc(sK2)
% 3.80/0.96      | ~ l1_pre_topc(sK3)
% 3.80/0.96      | ~ l1_pre_topc(sK2)
% 3.80/0.96      | ~ v1_funct_1(sK5) ),
% 3.80/0.96      inference(instantiation,[status(thm)],[c_37]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4043,plain,
% 3.80/0.96      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.80/0.96      | v5_pre_topc(sK5,sK2,sK3) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.80/0.96      | v2_pre_topc(sK3) != iProver_top
% 3.80/0.96      | v2_pre_topc(sK2) != iProver_top
% 3.80/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.80/0.96      | l1_pre_topc(sK2) != iProver_top
% 3.80/0.96      | v1_funct_1(sK5) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_4042]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4084,plain,
% 3.80/0.96      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.80/0.96      | ~ v2_pre_topc(sK3)
% 3.80/0.96      | ~ l1_pre_topc(sK3) ),
% 3.80/0.96      inference(instantiation,[status(thm)],[c_33]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4085,plain,
% 3.80/0.96      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.80/0.96      | v2_pre_topc(sK3) != iProver_top
% 3.80/0.96      | l1_pre_topc(sK3) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_4084]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4166,plain,
% 3.80/0.96      ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 3.80/0.96      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 3.80/0.96      inference(instantiation,[status(thm)],[c_31]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4167,plain,
% 3.80/0.96      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 3.80/0.96      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_4166]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4224,plain,
% 3.80/0.96      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 3.80/0.96      | ~ l1_pre_topc(sK3) ),
% 3.80/0.96      inference(instantiation,[status(thm)],[c_32]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_4225,plain,
% 3.80/0.96      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
% 3.80/0.96      | l1_pre_topc(sK3) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_4224]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_7077,plain,
% 3.80/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.80/0.96      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 3.80/0.96      inference(global_propositional_subsumption,
% 3.80/0.96                [status(thm)],
% 3.80/0.96                [c_6647,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,c_60,
% 3.80/0.96                 c_61,c_4011,c_4040,c_4043,c_4085,c_4167,c_4225]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_7078,plain,
% 3.80/0.96      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 3.80/0.96      inference(renaming,[status(thm)],[c_7077]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_7081,plain,
% 3.80/0.96      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.80/0.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 3.80/0.96      inference(global_propositional_subsumption,
% 3.80/0.96                [status(thm)],
% 3.80/0.96                [c_7078,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,c_60,
% 3.80/0.96                 c_4040,c_4043,c_4085,c_4167,c_4225]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_7086,plain,
% 3.80/0.96      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.80/0.96      | r1_tarski(k1_relat_1(sK5),u1_struct_0(sK2)) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_6750,c_7081]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_11495,plain,
% 3.80/0.96      ( v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.80/0.96      | r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) != iProver_top ),
% 3.80/0.96      inference(demodulation,[status(thm)],[c_10495,c_7086]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_7434,plain,
% 3.80/0.96      ( v1_funct_2(sK5,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top
% 3.80/0.96      | v1_partfun1(sK5,X0) != iProver_top
% 3.80/0.96      | r1_tarski(k1_relat_1(sK5),X0) != iProver_top
% 3.80/0.96      | v1_funct_1(sK5) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_6750,c_3950]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_7715,plain,
% 3.80/0.96      ( r1_tarski(k1_relat_1(sK5),X0) != iProver_top
% 3.80/0.96      | v1_partfun1(sK5,X0) != iProver_top
% 3.80/0.96      | v1_funct_2(sK5,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.80/0.96      inference(global_propositional_subsumption,[status(thm)],[c_7434,c_54]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_7716,plain,
% 3.80/0.96      ( v1_funct_2(sK5,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top
% 3.80/0.96      | v1_partfun1(sK5,X0) != iProver_top
% 3.80/0.96      | r1_tarski(k1_relat_1(sK5),X0) != iProver_top ),
% 3.80/0.96      inference(renaming,[status(thm)],[c_7715]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_7722,plain,
% 3.80/0.96      ( v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.80/0.96      | r1_tarski(k1_relat_1(sK5),u1_struct_0(sK2)) != iProver_top ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_7716,c_7086]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_11486,plain,
% 3.80/0.96      ( v1_partfun1(sK5,k1_relat_1(sK5)) != iProver_top
% 3.80/0.96      | r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) != iProver_top ),
% 3.80/0.96      inference(demodulation,[status(thm)],[c_10495,c_7722]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_12632,plain,
% 3.80/0.96      ( r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) != iProver_top ),
% 3.80/0.96      inference(global_propositional_subsumption,
% 3.80/0.96                [status(thm)],
% 3.80/0.96                [c_11495,c_59,c_4973,c_8257,c_11486]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_12636,plain,
% 3.80/0.96      ( $false ),
% 3.80/0.96      inference(superposition,[status(thm)],[c_3956,c_12632]) ).
% 3.80/0.96  
% 3.80/0.96  
% 3.80/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.80/0.96  
% 3.80/0.96  ------                               Statistics
% 3.80/0.96  
% 3.80/0.96  ------ General
% 3.80/0.96  
% 3.80/0.96  abstr_ref_over_cycles:                  0
% 3.80/0.96  abstr_ref_under_cycles:                 0
% 3.80/0.96  gc_basic_clause_elim:                   0
% 3.80/0.96  forced_gc_time:                         0
% 3.80/0.96  parsing_time:                           0.014
% 3.80/0.96  unif_index_cands_time:                  0.
% 3.80/0.96  unif_index_add_time:                    0.
% 3.80/0.96  orderings_time:                         0.
% 3.80/0.96  out_proof_time:                         0.018
% 3.80/0.96  total_time:                             0.43
% 3.80/0.96  num_of_symbols:                         57
% 3.80/0.96  num_of_terms:                           12513
% 3.80/0.96  
% 3.80/0.96  ------ Preprocessing
% 3.80/0.96  
% 3.80/0.96  num_of_splits:                          0
% 3.80/0.96  num_of_split_atoms:                     0
% 3.80/0.96  num_of_reused_defs:                     0
% 3.80/0.96  num_eq_ax_congr_red:                    24
% 3.80/0.96  num_of_sem_filtered_clauses:            1
% 3.80/0.96  num_of_subtypes:                        0
% 3.80/0.96  monotx_restored_types:                  0
% 3.80/0.96  sat_num_of_epr_types:                   0
% 3.80/0.96  sat_num_of_non_cyclic_types:            0
% 3.80/0.96  sat_guarded_non_collapsed_types:        0
% 3.80/0.96  num_pure_diseq_elim:                    0
% 3.80/0.96  simp_replaced_by:                       0
% 3.80/0.96  res_preprocessed:                       215
% 3.80/0.96  prep_upred:                             0
% 3.80/0.96  prep_unflattend:                        90
% 3.80/0.96  smt_new_axioms:                         0
% 3.80/0.96  pred_elim_cands:                        10
% 3.80/0.96  pred_elim:                              2
% 3.80/0.96  pred_elim_cl:                           2
% 3.80/0.96  pred_elim_cycles:                       10
% 3.80/0.96  merged_defs:                            8
% 3.80/0.96  merged_defs_ncl:                        0
% 3.80/0.96  bin_hyper_res:                          8
% 3.80/0.96  prep_cycles:                            4
% 3.80/0.96  pred_elim_time:                         0.043
% 3.80/0.96  splitting_time:                         0.
% 3.80/0.96  sem_filter_time:                        0.
% 3.80/0.96  monotx_time:                            0.
% 3.80/0.96  subtype_inf_time:                       0.
% 3.80/0.96  
% 3.80/0.96  ------ Problem properties
% 3.80/0.96  
% 3.80/0.96  clauses:                                44
% 3.80/0.96  conjectures:                            11
% 3.80/0.96  epr:                                    8
% 3.80/0.96  horn:                                   40
% 3.80/0.96  ground:                                 12
% 3.80/0.96  unary:                                  21
% 3.80/0.96  binary:                                 9
% 3.80/0.96  lits:                                   118
% 3.80/0.96  lits_eq:                                14
% 3.80/0.96  fd_pure:                                0
% 3.80/0.96  fd_pseudo:                              0
% 3.80/0.96  fd_cond:                                6
% 3.80/0.96  fd_pseudo_cond:                         2
% 3.80/0.96  ac_symbols:                             0
% 3.80/0.96  
% 3.80/0.96  ------ Propositional Solver
% 3.80/0.96  
% 3.80/0.96  prop_solver_calls:                      33
% 3.80/0.96  prop_fast_solver_calls:                 2628
% 3.80/0.96  smt_solver_calls:                       0
% 3.80/0.96  smt_fast_solver_calls:                  0
% 3.80/0.96  prop_num_of_clauses:                    5006
% 3.80/0.96  prop_preprocess_simplified:             11379
% 3.80/0.96  prop_fo_subsumed:                       121
% 3.80/0.96  prop_solver_time:                       0.
% 3.80/0.96  smt_solver_time:                        0.
% 3.80/0.96  smt_fast_solver_time:                   0.
% 3.80/0.96  prop_fast_solver_time:                  0.
% 3.80/0.96  prop_unsat_core_time:                   0.
% 3.80/0.96  
% 3.80/0.96  ------ QBF
% 3.80/0.96  
% 3.80/0.96  qbf_q_res:                              0
% 3.80/0.96  qbf_num_tautologies:                    0
% 3.80/0.96  qbf_prep_cycles:                        0
% 3.80/0.96  
% 3.80/0.96  ------ BMC1
% 3.80/0.96  
% 3.80/0.96  bmc1_current_bound:                     -1
% 3.80/0.96  bmc1_last_solved_bound:                 -1
% 3.80/0.96  bmc1_unsat_core_size:                   -1
% 3.80/0.96  bmc1_unsat_core_parents_size:           -1
% 3.80/0.96  bmc1_merge_next_fun:                    0
% 3.80/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.80/0.96  
% 3.80/0.96  ------ Instantiation
% 3.80/0.96  
% 3.80/0.96  inst_num_of_clauses:                    1372
% 3.80/0.96  inst_num_in_passive:                    155
% 3.80/0.96  inst_num_in_active:                     721
% 3.80/0.96  inst_num_in_unprocessed:                499
% 3.80/0.96  inst_num_of_loops:                      800
% 3.80/0.96  inst_num_of_learning_restarts:          0
% 3.80/0.96  inst_num_moves_active_passive:          74
% 3.80/0.96  inst_lit_activity:                      0
% 3.80/0.96  inst_lit_activity_moves:                0
% 3.80/0.96  inst_num_tautologies:                   0
% 3.80/0.96  inst_num_prop_implied:                  0
% 3.80/0.96  inst_num_existing_simplified:           0
% 3.80/0.96  inst_num_eq_res_simplified:             0
% 3.80/0.96  inst_num_child_elim:                    0
% 3.80/0.96  inst_num_of_dismatching_blockings:      287
% 3.80/0.96  inst_num_of_non_proper_insts:           1700
% 3.80/0.96  inst_num_of_duplicates:                 0
% 3.80/0.96  inst_inst_num_from_inst_to_res:         0
% 3.80/0.96  inst_dismatching_checking_time:         0.
% 3.80/0.96  
% 3.80/0.96  ------ Resolution
% 3.80/0.96  
% 3.80/0.96  res_num_of_clauses:                     0
% 3.80/0.96  res_num_in_passive:                     0
% 3.80/0.96  res_num_in_active:                      0
% 3.80/0.96  res_num_of_loops:                       219
% 3.80/0.96  res_forward_subset_subsumed:            87
% 3.80/0.96  res_backward_subset_subsumed:           6
% 3.80/0.96  res_forward_subsumed:                   0
% 3.80/0.96  res_backward_subsumed:                  0
% 3.80/0.96  res_forward_subsumption_resolution:     16
% 3.80/0.96  res_backward_subsumption_resolution:    0
% 3.80/0.96  res_clause_to_clause_subsumption:       902
% 3.80/0.96  res_orphan_elimination:                 0
% 3.80/0.96  res_tautology_del:                      124
% 3.80/0.96  res_num_eq_res_simplified:              0
% 3.80/0.96  res_num_sel_changes:                    0
% 3.80/0.96  res_moves_from_active_to_pass:          0
% 3.80/0.96  
% 3.80/0.96  ------ Superposition
% 3.80/0.96  
% 3.80/0.96  sup_time_total:                         0.
% 3.80/0.96  sup_time_generating:                    0.
% 3.80/0.96  sup_time_sim_full:                      0.
% 3.80/0.96  sup_time_sim_immed:                     0.
% 3.80/0.96  
% 3.80/0.96  sup_num_of_clauses:                     246
% 3.80/0.96  sup_num_in_active:                      106
% 3.80/0.96  sup_num_in_passive:                     140
% 3.80/0.96  sup_num_of_loops:                       158
% 3.80/0.96  sup_fw_superposition:                   281
% 3.80/0.96  sup_bw_superposition:                   259
% 3.80/0.96  sup_immediate_simplified:               233
% 3.80/0.96  sup_given_eliminated:                   1
% 3.80/0.96  comparisons_done:                       0
% 3.80/0.96  comparisons_avoided:                    9
% 3.80/0.96  
% 3.80/0.96  ------ Simplifications
% 3.80/0.96  
% 3.80/0.96  
% 3.80/0.96  sim_fw_subset_subsumed:                 129
% 3.80/0.96  sim_bw_subset_subsumed:                 105
% 3.80/0.96  sim_fw_subsumed:                        29
% 3.80/0.96  sim_bw_subsumed:                        4
% 3.80/0.96  sim_fw_subsumption_res:                 0
% 3.80/0.96  sim_bw_subsumption_res:                 0
% 3.80/0.96  sim_tautology_del:                      8
% 3.80/0.96  sim_eq_tautology_del:                   7
% 3.80/0.96  sim_eq_res_simp:                        0
% 3.80/0.96  sim_fw_demodulated:                     21
% 3.80/0.96  sim_bw_demodulated:                     28
% 3.80/0.96  sim_light_normalised:                   71
% 3.80/0.96  sim_joinable_taut:                      0
% 3.80/0.96  sim_joinable_simp:                      0
% 3.80/0.96  sim_ac_normalised:                      0
% 3.80/0.96  sim_smt_subsumption:                    0
% 3.80/0.96  
%------------------------------------------------------------------------------
