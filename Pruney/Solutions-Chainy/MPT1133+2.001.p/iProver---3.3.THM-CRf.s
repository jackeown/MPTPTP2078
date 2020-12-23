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

% Result     : Theorem 11.40s
% Output     : CNFRefutation 11.40s
% Verified   : 
% Statistics : Number of formulae       :  290 (831878 expanded)
%              Number of clauses        :  214 (189428 expanded)
%              Number of leaves         :   18 (250329 expanded)
%              Depth                    :   49
%              Number of atoms          : 1266 (9883459 expanded)
%              Number of equality atoms :  573 (1279917 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f44,f43,f42,f41])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f45])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
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
    inference(equality_resolution,[],[f66])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
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
    inference(equality_resolution,[],[f69])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
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
    inference(equality_resolution,[],[f67])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
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
    inference(equality_resolution,[],[f68])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2432,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2428,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3369,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2432,c_2428])).

cnf(c_10,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2425,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4821,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3369,c_2425])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2429,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4208,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3369,c_2429])).

cnf(c_6915,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2432,c_4208])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2430,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6943,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6915,c_2430])).

cnf(c_2860,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2432,c_2430])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2434,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3944,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_2434])).

cnf(c_6989,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6943,c_3944])).

cnf(c_11137,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4821,c_6989])).

cnf(c_11143,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2432,c_11137])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2406,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,negated_conjecture,
    ( sK2 = sK3 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2437,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2406,c_26])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2422,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5288,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_2422])).

cnf(c_3372,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2437,c_2428])).

cnf(c_5289,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5288,c_3372])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2405,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2436,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2405,c_26])).

cnf(c_5349,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5289,c_2436])).

cnf(c_5350,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_5349])).

cnf(c_5379,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5350,c_2437])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2426,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5486,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5379,c_2426])).

cnf(c_5380,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5350,c_2436])).

cnf(c_6118,plain,
    ( sK3 = k1_xboole_0
    | u1_struct_0(sK0) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5486,c_5380])).

cnf(c_6119,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6118])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2409,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5287,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2409,c_2422])).

cnf(c_3371,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2409,c_2428])).

cnf(c_5290,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5287,c_3371])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_5295,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5290])).

cnf(c_7106,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5290,c_28,c_5295])).

cnf(c_7107,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_7106])).

cnf(c_7144,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7107,c_2409])).

cnf(c_7380,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7144,c_2426])).

cnf(c_2408,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7145,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7107,c_2408])).

cnf(c_7727,plain,
    ( sK3 = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7380,c_7145])).

cnf(c_7728,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7727])).

cnf(c_7729,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6119,c_7728])).

cnf(c_7778,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7728,c_2408])).

cnf(c_7777,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7728,c_2409])).

cnf(c_21,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2414,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4697,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2409,c_2414])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_37,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_38,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_39,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_40,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_44,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_45,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2410,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2438,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2410,c_26])).

cnf(c_24,negated_conjecture,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2411,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2439,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2411,c_26])).

cnf(c_18,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2579,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2580,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2579])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2691,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2692,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2691])).

cnf(c_17,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2850,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2851,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2850])).

cnf(c_22,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2734,plain,
    ( ~ v5_pre_topc(sK3,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,X0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3221,plain,
    ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2734])).

cnf(c_3222,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3221])).

cnf(c_20,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2973,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
    | v5_pre_topc(sK3,sK0,X0)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3254,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2973])).

cnf(c_3255,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3254])).

cnf(c_23,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3170,plain,
    ( ~ v5_pre_topc(sK3,sK0,X0)
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_4676,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3170])).

cnf(c_4677,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4676])).

cnf(c_4826,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4697,c_37,c_38,c_39,c_40,c_44,c_45,c_46,c_2438,c_2439,c_2437,c_2436,c_2580,c_2692,c_2851,c_3222,c_3255,c_4677])).

cnf(c_4827,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4826])).

cnf(c_4830,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4827,c_37,c_38,c_39,c_40,c_44,c_45,c_46,c_2438,c_2437,c_2436,c_2580,c_2692,c_2851,c_3255,c_4677])).

cnf(c_6153,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6119,c_4830])).

cnf(c_8805,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
    | u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7777,c_6153])).

cnf(c_9216,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
    | u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6119,c_8805])).

cnf(c_14296,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
    | u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7729,c_7778,c_9216])).

cnf(c_14389,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14296,c_2409])).

cnf(c_4211,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2429,c_2430])).

cnf(c_14997,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14389,c_4211])).

cnf(c_15808,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_xboole_0
    | u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14997,c_3944])).

cnf(c_14387,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14296,c_3371])).

cnf(c_17926,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15808,c_14387])).

cnf(c_18037,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_17926,c_2437])).

cnf(c_18573,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18037,c_4211])).

cnf(c_19321,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18573,c_3944])).

cnf(c_18030,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17926,c_3372])).

cnf(c_20686,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19321,c_18030])).

cnf(c_20744,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_20686,c_7778])).

cnf(c_2636,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2761,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2636])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2998,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1594,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_4282,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != X2
    | u1_struct_0(sK0) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_7525,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != X1
    | u1_struct_0(sK0) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4282])).

cnf(c_11863,plain,
    ( ~ v1_funct_2(sK3,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(sK0) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_7525])).

cnf(c_11864,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(sK0) != X0
    | sK3 != sK3
    | v1_funct_2(sK3,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11863])).

cnf(c_11866,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(sK0) != k1_xboole_0
    | sK3 != sK3
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top
    | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11864])).

cnf(c_1588,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_19878,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_1588])).

cnf(c_6168,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6119,c_2436])).

cnf(c_20756,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20686,c_6168])).

cnf(c_4394,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1588])).

cnf(c_4267,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != X1
    | u1_struct_0(sK1) != X2
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_7492,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != X0
    | u1_struct_0(sK1) != X1
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4267])).

cnf(c_11827,plain,
    ( ~ v1_funct_2(sK3,X0,u1_struct_0(sK1))
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != X0
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_7492])).

cnf(c_11828,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != X0
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != sK3
    | v1_funct_2(sK3,X0,u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11827])).

cnf(c_11830,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_xboole_0
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != sK3
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11828])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2431,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2413,plain,
    ( v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3936,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2409,c_2413])).

cnf(c_2564,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2565,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2564])).

cnf(c_2679,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2680,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2679])).

cnf(c_2839,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2840,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2839])).

cnf(c_2412,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3180,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2409,c_2412])).

cnf(c_3245,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2973])).

cnf(c_3246,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3245])).

cnf(c_3564,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3180,c_37,c_38,c_39,c_40,c_44,c_45,c_2439,c_2437,c_2436,c_2565,c_2680,c_2840,c_3246])).

cnf(c_3565,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3564])).

cnf(c_4341,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3936,c_37,c_38,c_39,c_40,c_44,c_45,c_2439,c_2437,c_2436,c_2565,c_2680,c_2840,c_3180,c_3246])).

cnf(c_4342,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4341])).

cnf(c_5368,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5350,c_4342])).

cnf(c_4345,plain,
    ( v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2438,c_4342])).

cnf(c_3154,plain,
    ( ~ v5_pre_topc(sK3,X0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_4662,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3154])).

cnf(c_4663,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4662])).

cnf(c_5842,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5368,c_37,c_38,c_39,c_40,c_44,c_2437,c_2436,c_3565,c_4345,c_4663])).

cnf(c_5846,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_5842])).

cnf(c_14366,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14296,c_5846])).

cnf(c_2861,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_2430])).

cnf(c_6162,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6119,c_2861])).

cnf(c_20749,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_20686,c_6162])).

cnf(c_20853,plain,
    ( sK3 = k1_xboole_0
    | u1_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20756,c_2761,c_2998,c_4394,c_11830,c_14296,c_14366,c_20749])).

cnf(c_20854,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_20853])).

cnf(c_20951,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_20854,c_5379])).

cnf(c_5370,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5350,c_3565])).

cnf(c_7381,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7144,c_5370])).

cnf(c_7140,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7107,c_4830])).

cnf(c_7465,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7107,c_7140])).

cnf(c_9226,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7381,c_5379,c_5380,c_7465])).

cnf(c_2947,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2409,c_2430])).

cnf(c_9280,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9226,c_2947])).

cnf(c_20728,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_20686,c_9280])).

cnf(c_9282,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9226,c_2408])).

cnf(c_20733,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_20686,c_9282])).

cnf(c_4834,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_4830])).

cnf(c_20958,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20854,c_4834])).

cnf(c_22291,plain,
    ( sK3 = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20951,c_2761,c_2998,c_4394,c_11830,c_11866,c_14296,c_14366,c_19878,c_20728,c_20733,c_20749,c_20756,c_20958])).

cnf(c_22292,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_22291])).

cnf(c_22399,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22292,c_4830])).

cnf(c_24102,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7777,c_22399])).

cnf(c_25446,plain,
    ( sK3 = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20744,c_2761,c_2998,c_4394,c_11830,c_11866,c_14296,c_14366,c_19878,c_20749,c_20756,c_24102])).

cnf(c_25447,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_25446])).

cnf(c_25553,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_25447,c_2408])).

cnf(c_11829,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_xboole_0
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_11827])).

cnf(c_20967,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_20854,c_2861])).

cnf(c_21130,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_20967])).

cnf(c_20973,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20854,c_2436])).

cnf(c_21136,plain,
    ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1))
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_20973])).

cnf(c_25530,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25447,c_5846])).

cnf(c_25704,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_25530])).

cnf(c_25716,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25553,c_2761,c_2998,c_4394,c_11829,c_21130,c_21136,c_25447,c_25704])).

cnf(c_10727,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9226,c_5846])).

cnf(c_10795,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9226,c_10727])).

cnf(c_10861,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5350,c_10795])).

cnf(c_10865,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5350,c_10861])).

cnf(c_25763,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25716,c_10865])).

cnf(c_25891,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25763,c_6989])).

cnf(c_11146,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11143])).

cnf(c_29094,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25891,c_11146])).

cnf(c_29098,plain,
    ( u1_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2860,c_29094])).

cnf(c_25811,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25716,c_4834])).

cnf(c_26884,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_25811])).

cnf(c_33877,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29098,c_26884])).

cnf(c_42442,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_11143,c_33877])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:51:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.40/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.40/1.98  
% 11.40/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.40/1.98  
% 11.40/1.98  ------  iProver source info
% 11.40/1.98  
% 11.40/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.40/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.40/1.98  git: non_committed_changes: false
% 11.40/1.98  git: last_make_outside_of_git: false
% 11.40/1.98  
% 11.40/1.98  ------ 
% 11.40/1.98  
% 11.40/1.98  ------ Input Options
% 11.40/1.98  
% 11.40/1.98  --out_options                           all
% 11.40/1.98  --tptp_safe_out                         true
% 11.40/1.98  --problem_path                          ""
% 11.40/1.98  --include_path                          ""
% 11.40/1.98  --clausifier                            res/vclausify_rel
% 11.40/1.98  --clausifier_options                    ""
% 11.40/1.98  --stdin                                 false
% 11.40/1.98  --stats_out                             all
% 11.40/1.98  
% 11.40/1.98  ------ General Options
% 11.40/1.98  
% 11.40/1.98  --fof                                   false
% 11.40/1.98  --time_out_real                         305.
% 11.40/1.98  --time_out_virtual                      -1.
% 11.40/1.98  --symbol_type_check                     false
% 11.40/1.98  --clausify_out                          false
% 11.40/1.98  --sig_cnt_out                           false
% 11.40/1.98  --trig_cnt_out                          false
% 11.40/1.98  --trig_cnt_out_tolerance                1.
% 11.40/1.98  --trig_cnt_out_sk_spl                   false
% 11.40/1.98  --abstr_cl_out                          false
% 11.40/1.98  
% 11.40/1.98  ------ Global Options
% 11.40/1.98  
% 11.40/1.98  --schedule                              default
% 11.40/1.98  --add_important_lit                     false
% 11.40/1.98  --prop_solver_per_cl                    1000
% 11.40/1.98  --min_unsat_core                        false
% 11.40/1.98  --soft_assumptions                      false
% 11.40/1.98  --soft_lemma_size                       3
% 11.40/1.98  --prop_impl_unit_size                   0
% 11.40/1.98  --prop_impl_unit                        []
% 11.40/1.98  --share_sel_clauses                     true
% 11.40/1.98  --reset_solvers                         false
% 11.40/1.98  --bc_imp_inh                            [conj_cone]
% 11.40/1.98  --conj_cone_tolerance                   3.
% 11.40/1.98  --extra_neg_conj                        none
% 11.40/1.98  --large_theory_mode                     true
% 11.40/1.98  --prolific_symb_bound                   200
% 11.40/1.98  --lt_threshold                          2000
% 11.40/1.98  --clause_weak_htbl                      true
% 11.40/1.98  --gc_record_bc_elim                     false
% 11.40/1.98  
% 11.40/1.98  ------ Preprocessing Options
% 11.40/1.98  
% 11.40/1.98  --preprocessing_flag                    true
% 11.40/1.98  --time_out_prep_mult                    0.1
% 11.40/1.98  --splitting_mode                        input
% 11.40/1.98  --splitting_grd                         true
% 11.40/1.98  --splitting_cvd                         false
% 11.40/1.98  --splitting_cvd_svl                     false
% 11.40/1.98  --splitting_nvd                         32
% 11.40/1.98  --sub_typing                            true
% 11.40/1.98  --prep_gs_sim                           true
% 11.40/1.98  --prep_unflatten                        true
% 11.40/1.98  --prep_res_sim                          true
% 11.40/1.98  --prep_upred                            true
% 11.40/1.98  --prep_sem_filter                       exhaustive
% 11.40/1.98  --prep_sem_filter_out                   false
% 11.40/1.98  --pred_elim                             true
% 11.40/1.98  --res_sim_input                         true
% 11.40/1.98  --eq_ax_congr_red                       true
% 11.40/1.98  --pure_diseq_elim                       true
% 11.40/1.98  --brand_transform                       false
% 11.40/1.98  --non_eq_to_eq                          false
% 11.40/1.98  --prep_def_merge                        true
% 11.40/1.98  --prep_def_merge_prop_impl              false
% 11.40/1.98  --prep_def_merge_mbd                    true
% 11.40/1.98  --prep_def_merge_tr_red                 false
% 11.40/1.98  --prep_def_merge_tr_cl                  false
% 11.40/1.98  --smt_preprocessing                     true
% 11.40/1.98  --smt_ac_axioms                         fast
% 11.40/1.98  --preprocessed_out                      false
% 11.40/1.98  --preprocessed_stats                    false
% 11.40/1.98  
% 11.40/1.98  ------ Abstraction refinement Options
% 11.40/1.98  
% 11.40/1.98  --abstr_ref                             []
% 11.40/1.98  --abstr_ref_prep                        false
% 11.40/1.98  --abstr_ref_until_sat                   false
% 11.40/1.98  --abstr_ref_sig_restrict                funpre
% 11.40/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.40/1.98  --abstr_ref_under                       []
% 11.40/1.98  
% 11.40/1.98  ------ SAT Options
% 11.40/1.98  
% 11.40/1.98  --sat_mode                              false
% 11.40/1.98  --sat_fm_restart_options                ""
% 11.40/1.98  --sat_gr_def                            false
% 11.40/1.98  --sat_epr_types                         true
% 11.40/1.98  --sat_non_cyclic_types                  false
% 11.40/1.98  --sat_finite_models                     false
% 11.40/1.98  --sat_fm_lemmas                         false
% 11.40/1.98  --sat_fm_prep                           false
% 11.40/1.98  --sat_fm_uc_incr                        true
% 11.40/1.98  --sat_out_model                         small
% 11.40/1.98  --sat_out_clauses                       false
% 11.40/1.98  
% 11.40/1.98  ------ QBF Options
% 11.40/1.98  
% 11.40/1.98  --qbf_mode                              false
% 11.40/1.98  --qbf_elim_univ                         false
% 11.40/1.98  --qbf_dom_inst                          none
% 11.40/1.98  --qbf_dom_pre_inst                      false
% 11.40/1.98  --qbf_sk_in                             false
% 11.40/1.98  --qbf_pred_elim                         true
% 11.40/1.98  --qbf_split                             512
% 11.40/1.98  
% 11.40/1.98  ------ BMC1 Options
% 11.40/1.98  
% 11.40/1.98  --bmc1_incremental                      false
% 11.40/1.98  --bmc1_axioms                           reachable_all
% 11.40/1.98  --bmc1_min_bound                        0
% 11.40/1.98  --bmc1_max_bound                        -1
% 11.40/1.98  --bmc1_max_bound_default                -1
% 11.40/1.98  --bmc1_symbol_reachability              true
% 11.40/1.98  --bmc1_property_lemmas                  false
% 11.40/1.98  --bmc1_k_induction                      false
% 11.40/1.98  --bmc1_non_equiv_states                 false
% 11.40/1.98  --bmc1_deadlock                         false
% 11.40/1.98  --bmc1_ucm                              false
% 11.40/1.98  --bmc1_add_unsat_core                   none
% 11.40/1.98  --bmc1_unsat_core_children              false
% 11.40/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.40/1.98  --bmc1_out_stat                         full
% 11.40/1.98  --bmc1_ground_init                      false
% 11.40/1.98  --bmc1_pre_inst_next_state              false
% 11.40/1.98  --bmc1_pre_inst_state                   false
% 11.40/1.98  --bmc1_pre_inst_reach_state             false
% 11.40/1.98  --bmc1_out_unsat_core                   false
% 11.40/1.98  --bmc1_aig_witness_out                  false
% 11.40/1.98  --bmc1_verbose                          false
% 11.40/1.98  --bmc1_dump_clauses_tptp                false
% 11.40/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.40/1.98  --bmc1_dump_file                        -
% 11.40/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.40/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.40/1.98  --bmc1_ucm_extend_mode                  1
% 11.40/1.98  --bmc1_ucm_init_mode                    2
% 11.40/1.98  --bmc1_ucm_cone_mode                    none
% 11.40/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.40/1.98  --bmc1_ucm_relax_model                  4
% 11.40/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.40/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.40/1.98  --bmc1_ucm_layered_model                none
% 11.40/1.98  --bmc1_ucm_max_lemma_size               10
% 11.40/1.98  
% 11.40/1.98  ------ AIG Options
% 11.40/1.98  
% 11.40/1.98  --aig_mode                              false
% 11.40/1.98  
% 11.40/1.98  ------ Instantiation Options
% 11.40/1.98  
% 11.40/1.98  --instantiation_flag                    true
% 11.40/1.98  --inst_sos_flag                         true
% 11.40/1.98  --inst_sos_phase                        true
% 11.40/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.40/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.40/1.98  --inst_lit_sel_side                     num_symb
% 11.40/1.98  --inst_solver_per_active                1400
% 11.40/1.98  --inst_solver_calls_frac                1.
% 11.40/1.98  --inst_passive_queue_type               priority_queues
% 11.40/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.40/1.98  --inst_passive_queues_freq              [25;2]
% 11.40/1.98  --inst_dismatching                      true
% 11.40/1.98  --inst_eager_unprocessed_to_passive     true
% 11.40/1.98  --inst_prop_sim_given                   true
% 11.40/1.98  --inst_prop_sim_new                     false
% 11.40/1.98  --inst_subs_new                         false
% 11.40/1.98  --inst_eq_res_simp                      false
% 11.40/1.98  --inst_subs_given                       false
% 11.40/1.98  --inst_orphan_elimination               true
% 11.40/1.98  --inst_learning_loop_flag               true
% 11.40/1.98  --inst_learning_start                   3000
% 11.40/1.98  --inst_learning_factor                  2
% 11.40/1.98  --inst_start_prop_sim_after_learn       3
% 11.40/1.98  --inst_sel_renew                        solver
% 11.40/1.98  --inst_lit_activity_flag                true
% 11.40/1.98  --inst_restr_to_given                   false
% 11.40/1.98  --inst_activity_threshold               500
% 11.40/1.98  --inst_out_proof                        true
% 11.40/1.98  
% 11.40/1.98  ------ Resolution Options
% 11.40/1.98  
% 11.40/1.98  --resolution_flag                       true
% 11.40/1.98  --res_lit_sel                           adaptive
% 11.40/1.98  --res_lit_sel_side                      none
% 11.40/1.98  --res_ordering                          kbo
% 11.40/1.98  --res_to_prop_solver                    active
% 11.40/1.98  --res_prop_simpl_new                    false
% 11.40/1.98  --res_prop_simpl_given                  true
% 11.40/1.98  --res_passive_queue_type                priority_queues
% 11.40/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.40/1.98  --res_passive_queues_freq               [15;5]
% 11.40/1.98  --res_forward_subs                      full
% 11.40/1.98  --res_backward_subs                     full
% 11.40/1.98  --res_forward_subs_resolution           true
% 11.40/1.98  --res_backward_subs_resolution          true
% 11.40/1.98  --res_orphan_elimination                true
% 11.40/1.98  --res_time_limit                        2.
% 11.40/1.98  --res_out_proof                         true
% 11.40/1.98  
% 11.40/1.98  ------ Superposition Options
% 11.40/1.98  
% 11.40/1.98  --superposition_flag                    true
% 11.40/1.98  --sup_passive_queue_type                priority_queues
% 11.40/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.40/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.40/1.98  --demod_completeness_check              fast
% 11.40/1.98  --demod_use_ground                      true
% 11.40/1.98  --sup_to_prop_solver                    passive
% 11.40/1.98  --sup_prop_simpl_new                    true
% 11.40/1.98  --sup_prop_simpl_given                  true
% 11.40/1.98  --sup_fun_splitting                     true
% 11.40/1.98  --sup_smt_interval                      50000
% 11.40/1.98  
% 11.40/1.98  ------ Superposition Simplification Setup
% 11.40/1.98  
% 11.40/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.40/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.40/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.40/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.40/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.40/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.40/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.40/1.98  --sup_immed_triv                        [TrivRules]
% 11.40/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.40/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.40/1.98  --sup_immed_bw_main                     []
% 11.40/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.40/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.40/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.40/1.98  --sup_input_bw                          []
% 11.40/1.98  
% 11.40/1.98  ------ Combination Options
% 11.40/1.98  
% 11.40/1.98  --comb_res_mult                         3
% 11.40/1.98  --comb_sup_mult                         2
% 11.40/1.98  --comb_inst_mult                        10
% 11.40/1.98  
% 11.40/1.98  ------ Debug Options
% 11.40/1.98  
% 11.40/1.98  --dbg_backtrace                         false
% 11.40/1.98  --dbg_dump_prop_clauses                 false
% 11.40/1.98  --dbg_dump_prop_clauses_file            -
% 11.40/1.98  --dbg_out_stat                          false
% 11.40/1.98  ------ Parsing...
% 11.40/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.40/1.98  
% 11.40/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.40/1.98  
% 11.40/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.40/1.98  
% 11.40/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.40/1.98  ------ Proving...
% 11.40/1.98  ------ Problem Properties 
% 11.40/1.98  
% 11.40/1.98  
% 11.40/1.98  clauses                                 36
% 11.40/1.98  conjectures                             13
% 11.40/1.98  EPR                                     9
% 11.40/1.98  Horn                                    31
% 11.40/1.98  unary                                   13
% 11.40/1.98  binary                                  9
% 11.40/1.98  lits                                    108
% 11.40/1.98  lits eq                                 13
% 11.40/1.98  fd_pure                                 0
% 11.40/1.98  fd_pseudo                               0
% 11.40/1.98  fd_cond                                 3
% 11.40/1.98  fd_pseudo_cond                          1
% 11.40/1.98  AC symbols                              0
% 11.40/1.98  
% 11.40/1.98  ------ Schedule dynamic 5 is on 
% 11.40/1.98  
% 11.40/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.40/1.98  
% 11.40/1.98  
% 11.40/1.98  ------ 
% 11.40/1.98  Current options:
% 11.40/1.98  ------ 
% 11.40/1.98  
% 11.40/1.98  ------ Input Options
% 11.40/1.98  
% 11.40/1.98  --out_options                           all
% 11.40/1.98  --tptp_safe_out                         true
% 11.40/1.98  --problem_path                          ""
% 11.40/1.98  --include_path                          ""
% 11.40/1.98  --clausifier                            res/vclausify_rel
% 11.40/1.98  --clausifier_options                    ""
% 11.40/1.98  --stdin                                 false
% 11.40/1.98  --stats_out                             all
% 11.40/1.98  
% 11.40/1.98  ------ General Options
% 11.40/1.98  
% 11.40/1.98  --fof                                   false
% 11.40/1.98  --time_out_real                         305.
% 11.40/1.98  --time_out_virtual                      -1.
% 11.40/1.98  --symbol_type_check                     false
% 11.40/1.98  --clausify_out                          false
% 11.40/1.98  --sig_cnt_out                           false
% 11.40/1.98  --trig_cnt_out                          false
% 11.40/1.98  --trig_cnt_out_tolerance                1.
% 11.40/1.98  --trig_cnt_out_sk_spl                   false
% 11.40/1.98  --abstr_cl_out                          false
% 11.40/1.98  
% 11.40/1.98  ------ Global Options
% 11.40/1.98  
% 11.40/1.98  --schedule                              default
% 11.40/1.98  --add_important_lit                     false
% 11.40/1.98  --prop_solver_per_cl                    1000
% 11.40/1.98  --min_unsat_core                        false
% 11.40/1.98  --soft_assumptions                      false
% 11.40/1.98  --soft_lemma_size                       3
% 11.40/1.98  --prop_impl_unit_size                   0
% 11.40/1.98  --prop_impl_unit                        []
% 11.40/1.98  --share_sel_clauses                     true
% 11.40/1.98  --reset_solvers                         false
% 11.40/1.98  --bc_imp_inh                            [conj_cone]
% 11.40/1.98  --conj_cone_tolerance                   3.
% 11.40/1.98  --extra_neg_conj                        none
% 11.40/1.98  --large_theory_mode                     true
% 11.40/1.98  --prolific_symb_bound                   200
% 11.40/1.98  --lt_threshold                          2000
% 11.40/1.98  --clause_weak_htbl                      true
% 11.40/1.98  --gc_record_bc_elim                     false
% 11.40/1.98  
% 11.40/1.98  ------ Preprocessing Options
% 11.40/1.98  
% 11.40/1.98  --preprocessing_flag                    true
% 11.40/1.98  --time_out_prep_mult                    0.1
% 11.40/1.98  --splitting_mode                        input
% 11.40/1.98  --splitting_grd                         true
% 11.40/1.98  --splitting_cvd                         false
% 11.40/1.98  --splitting_cvd_svl                     false
% 11.40/1.98  --splitting_nvd                         32
% 11.40/1.98  --sub_typing                            true
% 11.40/1.98  --prep_gs_sim                           true
% 11.40/1.98  --prep_unflatten                        true
% 11.40/1.98  --prep_res_sim                          true
% 11.40/1.98  --prep_upred                            true
% 11.40/1.98  --prep_sem_filter                       exhaustive
% 11.40/1.98  --prep_sem_filter_out                   false
% 11.40/1.98  --pred_elim                             true
% 11.40/1.98  --res_sim_input                         true
% 11.40/1.98  --eq_ax_congr_red                       true
% 11.40/1.98  --pure_diseq_elim                       true
% 11.40/1.98  --brand_transform                       false
% 11.40/1.98  --non_eq_to_eq                          false
% 11.40/1.98  --prep_def_merge                        true
% 11.40/1.98  --prep_def_merge_prop_impl              false
% 11.40/1.98  --prep_def_merge_mbd                    true
% 11.40/1.98  --prep_def_merge_tr_red                 false
% 11.40/1.98  --prep_def_merge_tr_cl                  false
% 11.40/1.98  --smt_preprocessing                     true
% 11.40/1.98  --smt_ac_axioms                         fast
% 11.40/1.98  --preprocessed_out                      false
% 11.40/1.98  --preprocessed_stats                    false
% 11.40/1.98  
% 11.40/1.98  ------ Abstraction refinement Options
% 11.40/1.98  
% 11.40/1.98  --abstr_ref                             []
% 11.40/1.98  --abstr_ref_prep                        false
% 11.40/1.98  --abstr_ref_until_sat                   false
% 11.40/1.98  --abstr_ref_sig_restrict                funpre
% 11.40/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.40/1.98  --abstr_ref_under                       []
% 11.40/1.98  
% 11.40/1.98  ------ SAT Options
% 11.40/1.98  
% 11.40/1.98  --sat_mode                              false
% 11.40/1.98  --sat_fm_restart_options                ""
% 11.40/1.98  --sat_gr_def                            false
% 11.40/1.98  --sat_epr_types                         true
% 11.40/1.98  --sat_non_cyclic_types                  false
% 11.40/1.98  --sat_finite_models                     false
% 11.40/1.98  --sat_fm_lemmas                         false
% 11.40/1.98  --sat_fm_prep                           false
% 11.40/1.98  --sat_fm_uc_incr                        true
% 11.40/1.98  --sat_out_model                         small
% 11.40/1.98  --sat_out_clauses                       false
% 11.40/1.98  
% 11.40/1.98  ------ QBF Options
% 11.40/1.98  
% 11.40/1.98  --qbf_mode                              false
% 11.40/1.98  --qbf_elim_univ                         false
% 11.40/1.98  --qbf_dom_inst                          none
% 11.40/1.98  --qbf_dom_pre_inst                      false
% 11.40/1.98  --qbf_sk_in                             false
% 11.40/1.98  --qbf_pred_elim                         true
% 11.40/1.98  --qbf_split                             512
% 11.40/1.98  
% 11.40/1.98  ------ BMC1 Options
% 11.40/1.98  
% 11.40/1.98  --bmc1_incremental                      false
% 11.40/1.98  --bmc1_axioms                           reachable_all
% 11.40/1.98  --bmc1_min_bound                        0
% 11.40/1.98  --bmc1_max_bound                        -1
% 11.40/1.98  --bmc1_max_bound_default                -1
% 11.40/1.98  --bmc1_symbol_reachability              true
% 11.40/1.98  --bmc1_property_lemmas                  false
% 11.40/1.98  --bmc1_k_induction                      false
% 11.40/1.98  --bmc1_non_equiv_states                 false
% 11.40/1.98  --bmc1_deadlock                         false
% 11.40/1.98  --bmc1_ucm                              false
% 11.40/1.98  --bmc1_add_unsat_core                   none
% 11.40/1.98  --bmc1_unsat_core_children              false
% 11.40/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.40/1.98  --bmc1_out_stat                         full
% 11.40/1.98  --bmc1_ground_init                      false
% 11.40/1.98  --bmc1_pre_inst_next_state              false
% 11.40/1.98  --bmc1_pre_inst_state                   false
% 11.40/1.98  --bmc1_pre_inst_reach_state             false
% 11.40/1.98  --bmc1_out_unsat_core                   false
% 11.40/1.98  --bmc1_aig_witness_out                  false
% 11.40/1.98  --bmc1_verbose                          false
% 11.40/1.98  --bmc1_dump_clauses_tptp                false
% 11.40/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.40/1.98  --bmc1_dump_file                        -
% 11.40/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.40/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.40/1.98  --bmc1_ucm_extend_mode                  1
% 11.40/1.98  --bmc1_ucm_init_mode                    2
% 11.40/1.98  --bmc1_ucm_cone_mode                    none
% 11.40/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.40/1.98  --bmc1_ucm_relax_model                  4
% 11.40/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.40/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.40/1.98  --bmc1_ucm_layered_model                none
% 11.40/1.98  --bmc1_ucm_max_lemma_size               10
% 11.40/1.98  
% 11.40/1.98  ------ AIG Options
% 11.40/1.98  
% 11.40/1.98  --aig_mode                              false
% 11.40/1.98  
% 11.40/1.98  ------ Instantiation Options
% 11.40/1.98  
% 11.40/1.98  --instantiation_flag                    true
% 11.40/1.98  --inst_sos_flag                         true
% 11.40/1.98  --inst_sos_phase                        true
% 11.40/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.40/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.40/1.98  --inst_lit_sel_side                     none
% 11.40/1.98  --inst_solver_per_active                1400
% 11.40/1.98  --inst_solver_calls_frac                1.
% 11.40/1.98  --inst_passive_queue_type               priority_queues
% 11.40/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.40/1.98  --inst_passive_queues_freq              [25;2]
% 11.40/1.98  --inst_dismatching                      true
% 11.40/1.98  --inst_eager_unprocessed_to_passive     true
% 11.40/1.98  --inst_prop_sim_given                   true
% 11.40/1.98  --inst_prop_sim_new                     false
% 11.40/1.98  --inst_subs_new                         false
% 11.40/1.98  --inst_eq_res_simp                      false
% 11.40/1.98  --inst_subs_given                       false
% 11.40/1.98  --inst_orphan_elimination               true
% 11.40/1.98  --inst_learning_loop_flag               true
% 11.40/1.98  --inst_learning_start                   3000
% 11.40/1.98  --inst_learning_factor                  2
% 11.40/1.98  --inst_start_prop_sim_after_learn       3
% 11.40/1.98  --inst_sel_renew                        solver
% 11.40/1.98  --inst_lit_activity_flag                true
% 11.40/1.98  --inst_restr_to_given                   false
% 11.40/1.98  --inst_activity_threshold               500
% 11.40/1.98  --inst_out_proof                        true
% 11.40/1.98  
% 11.40/1.98  ------ Resolution Options
% 11.40/1.98  
% 11.40/1.98  --resolution_flag                       false
% 11.40/1.98  --res_lit_sel                           adaptive
% 11.40/1.98  --res_lit_sel_side                      none
% 11.40/1.98  --res_ordering                          kbo
% 11.40/1.98  --res_to_prop_solver                    active
% 11.40/1.98  --res_prop_simpl_new                    false
% 11.40/1.98  --res_prop_simpl_given                  true
% 11.40/1.98  --res_passive_queue_type                priority_queues
% 11.40/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.40/1.98  --res_passive_queues_freq               [15;5]
% 11.40/1.98  --res_forward_subs                      full
% 11.40/1.98  --res_backward_subs                     full
% 11.40/1.98  --res_forward_subs_resolution           true
% 11.40/1.98  --res_backward_subs_resolution          true
% 11.40/1.98  --res_orphan_elimination                true
% 11.40/1.98  --res_time_limit                        2.
% 11.40/1.98  --res_out_proof                         true
% 11.40/1.98  
% 11.40/1.98  ------ Superposition Options
% 11.40/1.98  
% 11.40/1.98  --superposition_flag                    true
% 11.40/1.98  --sup_passive_queue_type                priority_queues
% 11.40/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.40/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.40/1.98  --demod_completeness_check              fast
% 11.40/1.98  --demod_use_ground                      true
% 11.40/1.98  --sup_to_prop_solver                    passive
% 11.40/1.98  --sup_prop_simpl_new                    true
% 11.40/1.98  --sup_prop_simpl_given                  true
% 11.40/1.98  --sup_fun_splitting                     true
% 11.40/1.98  --sup_smt_interval                      50000
% 11.40/1.98  
% 11.40/1.98  ------ Superposition Simplification Setup
% 11.40/1.98  
% 11.40/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.40/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.40/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.40/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.40/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.40/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.40/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.40/1.98  --sup_immed_triv                        [TrivRules]
% 11.40/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.40/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.40/1.98  --sup_immed_bw_main                     []
% 11.40/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.40/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.40/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.40/1.98  --sup_input_bw                          []
% 11.40/1.98  
% 11.40/1.98  ------ Combination Options
% 11.40/1.98  
% 11.40/1.98  --comb_res_mult                         3
% 11.40/1.98  --comb_sup_mult                         2
% 11.40/1.98  --comb_inst_mult                        10
% 11.40/1.98  
% 11.40/1.98  ------ Debug Options
% 11.40/1.98  
% 11.40/1.98  --dbg_backtrace                         false
% 11.40/1.98  --dbg_dump_prop_clauses                 false
% 11.40/1.98  --dbg_dump_prop_clauses_file            -
% 11.40/1.98  --dbg_out_stat                          false
% 11.40/1.98  
% 11.40/1.98  
% 11.40/1.98  
% 11.40/1.98  
% 11.40/1.98  ------ Proving...
% 11.40/1.98  
% 11.40/1.98  
% 11.40/1.98  % SZS status Theorem for theBenchmark.p
% 11.40/1.98  
% 11.40/1.98   Resolution empty clause
% 11.40/1.98  
% 11.40/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.40/1.98  
% 11.40/1.98  fof(f2,axiom,(
% 11.40/1.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f49,plain,(
% 11.40/1.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.40/1.98    inference(cnf_transformation,[],[f2])).
% 11.40/1.98  
% 11.40/1.98  fof(f6,axiom,(
% 11.40/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f18,plain,(
% 11.40/1.98    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.40/1.98    inference(ennf_transformation,[],[f6])).
% 11.40/1.98  
% 11.40/1.98  fof(f53,plain,(
% 11.40/1.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.40/1.98    inference(cnf_transformation,[],[f18])).
% 11.40/1.98  
% 11.40/1.98  fof(f7,axiom,(
% 11.40/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f19,plain,(
% 11.40/1.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.40/1.98    inference(ennf_transformation,[],[f7])).
% 11.40/1.98  
% 11.40/1.98  fof(f20,plain,(
% 11.40/1.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.40/1.98    inference(flattening,[],[f19])).
% 11.40/1.98  
% 11.40/1.98  fof(f36,plain,(
% 11.40/1.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.40/1.98    inference(nnf_transformation,[],[f20])).
% 11.40/1.98  
% 11.40/1.98  fof(f57,plain,(
% 11.40/1.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.40/1.98    inference(cnf_transformation,[],[f36])).
% 11.40/1.98  
% 11.40/1.98  fof(f88,plain,(
% 11.40/1.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 11.40/1.98    inference(equality_resolution,[],[f57])).
% 11.40/1.98  
% 11.40/1.98  fof(f5,axiom,(
% 11.40/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f17,plain,(
% 11.40/1.98    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.40/1.98    inference(ennf_transformation,[],[f5])).
% 11.40/1.98  
% 11.40/1.98  fof(f52,plain,(
% 11.40/1.98    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.40/1.98    inference(cnf_transformation,[],[f17])).
% 11.40/1.98  
% 11.40/1.98  fof(f3,axiom,(
% 11.40/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f35,plain,(
% 11.40/1.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.40/1.98    inference(nnf_transformation,[],[f3])).
% 11.40/1.98  
% 11.40/1.98  fof(f50,plain,(
% 11.40/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.40/1.98    inference(cnf_transformation,[],[f35])).
% 11.40/1.98  
% 11.40/1.98  fof(f1,axiom,(
% 11.40/1.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f33,plain,(
% 11.40/1.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.40/1.98    inference(nnf_transformation,[],[f1])).
% 11.40/1.98  
% 11.40/1.98  fof(f34,plain,(
% 11.40/1.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.40/1.98    inference(flattening,[],[f33])).
% 11.40/1.98  
% 11.40/1.98  fof(f48,plain,(
% 11.40/1.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f34])).
% 11.40/1.98  
% 11.40/1.98  fof(f14,conjecture,(
% 11.40/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f15,negated_conjecture,(
% 11.40/1.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 11.40/1.98    inference(negated_conjecture,[],[f14])).
% 11.40/1.98  
% 11.40/1.98  fof(f31,plain,(
% 11.40/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.40/1.98    inference(ennf_transformation,[],[f15])).
% 11.40/1.98  
% 11.40/1.98  fof(f32,plain,(
% 11.40/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.40/1.98    inference(flattening,[],[f31])).
% 11.40/1.98  
% 11.40/1.98  fof(f39,plain,(
% 11.40/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.40/1.98    inference(nnf_transformation,[],[f32])).
% 11.40/1.98  
% 11.40/1.98  fof(f40,plain,(
% 11.40/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.40/1.98    inference(flattening,[],[f39])).
% 11.40/1.98  
% 11.40/1.98  fof(f44,plain,(
% 11.40/1.98    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK3 = X2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK3))) )),
% 11.40/1.98    introduced(choice_axiom,[])).
% 11.40/1.98  
% 11.40/1.98  fof(f43,plain,(
% 11.40/1.98    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 11.40/1.98    introduced(choice_axiom,[])).
% 11.40/1.98  
% 11.40/1.98  fof(f42,plain,(
% 11.40/1.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,X0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,X0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 11.40/1.98    introduced(choice_axiom,[])).
% 11.40/1.98  
% 11.40/1.98  fof(f41,plain,(
% 11.40/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.40/1.98    introduced(choice_axiom,[])).
% 11.40/1.98  
% 11.40/1.98  fof(f45,plain,(
% 11.40/1.98    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.40/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f44,f43,f42,f41])).
% 11.40/1.98  
% 11.40/1.98  fof(f76,plain,(
% 11.40/1.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 11.40/1.98    inference(cnf_transformation,[],[f45])).
% 11.40/1.98  
% 11.40/1.98  fof(f80,plain,(
% 11.40/1.98    sK2 = sK3),
% 11.40/1.98    inference(cnf_transformation,[],[f45])).
% 11.40/1.98  
% 11.40/1.98  fof(f54,plain,(
% 11.40/1.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.40/1.98    inference(cnf_transformation,[],[f36])).
% 11.40/1.98  
% 11.40/1.98  fof(f75,plain,(
% 11.40/1.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 11.40/1.98    inference(cnf_transformation,[],[f45])).
% 11.40/1.98  
% 11.40/1.98  fof(f58,plain,(
% 11.40/1.98    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.40/1.98    inference(cnf_transformation,[],[f36])).
% 11.40/1.98  
% 11.40/1.98  fof(f87,plain,(
% 11.40/1.98    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 11.40/1.98    inference(equality_resolution,[],[f58])).
% 11.40/1.98  
% 11.40/1.98  fof(f79,plain,(
% 11.40/1.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 11.40/1.98    inference(cnf_transformation,[],[f45])).
% 11.40/1.98  
% 11.40/1.98  fof(f78,plain,(
% 11.40/1.98    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 11.40/1.98    inference(cnf_transformation,[],[f45])).
% 11.40/1.98  
% 11.40/1.98  fof(f12,axiom,(
% 11.40/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f27,plain,(
% 11.40/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.40/1.98    inference(ennf_transformation,[],[f12])).
% 11.40/1.98  
% 11.40/1.98  fof(f28,plain,(
% 11.40/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.40/1.98    inference(flattening,[],[f27])).
% 11.40/1.98  
% 11.40/1.98  fof(f37,plain,(
% 11.40/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.40/1.98    inference(nnf_transformation,[],[f28])).
% 11.40/1.98  
% 11.40/1.98  fof(f66,plain,(
% 11.40/1.98    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f37])).
% 11.40/1.98  
% 11.40/1.98  fof(f91,plain,(
% 11.40/1.98    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.40/1.98    inference(equality_resolution,[],[f66])).
% 11.40/1.98  
% 11.40/1.98  fof(f70,plain,(
% 11.40/1.98    v2_pre_topc(sK0)),
% 11.40/1.98    inference(cnf_transformation,[],[f45])).
% 11.40/1.98  
% 11.40/1.98  fof(f71,plain,(
% 11.40/1.98    l1_pre_topc(sK0)),
% 11.40/1.98    inference(cnf_transformation,[],[f45])).
% 11.40/1.98  
% 11.40/1.98  fof(f72,plain,(
% 11.40/1.98    v2_pre_topc(sK1)),
% 11.40/1.98    inference(cnf_transformation,[],[f45])).
% 11.40/1.98  
% 11.40/1.98  fof(f73,plain,(
% 11.40/1.98    l1_pre_topc(sK1)),
% 11.40/1.98    inference(cnf_transformation,[],[f45])).
% 11.40/1.98  
% 11.40/1.98  fof(f77,plain,(
% 11.40/1.98    v1_funct_1(sK3)),
% 11.40/1.98    inference(cnf_transformation,[],[f45])).
% 11.40/1.98  
% 11.40/1.98  fof(f81,plain,(
% 11.40/1.98    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 11.40/1.98    inference(cnf_transformation,[],[f45])).
% 11.40/1.98  
% 11.40/1.98  fof(f82,plain,(
% 11.40/1.98    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 11.40/1.98    inference(cnf_transformation,[],[f45])).
% 11.40/1.98  
% 11.40/1.98  fof(f11,axiom,(
% 11.40/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f25,plain,(
% 11.40/1.98    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.40/1.98    inference(ennf_transformation,[],[f11])).
% 11.40/1.98  
% 11.40/1.98  fof(f26,plain,(
% 11.40/1.98    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.40/1.98    inference(flattening,[],[f25])).
% 11.40/1.98  
% 11.40/1.98  fof(f65,plain,(
% 11.40/1.98    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f26])).
% 11.40/1.98  
% 11.40/1.98  fof(f9,axiom,(
% 11.40/1.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f23,plain,(
% 11.40/1.98    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.40/1.98    inference(ennf_transformation,[],[f9])).
% 11.40/1.98  
% 11.40/1.98  fof(f62,plain,(
% 11.40/1.98    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.40/1.98    inference(cnf_transformation,[],[f23])).
% 11.40/1.98  
% 11.40/1.98  fof(f10,axiom,(
% 11.40/1.98    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f24,plain,(
% 11.40/1.98    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.40/1.98    inference(ennf_transformation,[],[f10])).
% 11.40/1.98  
% 11.40/1.98  fof(f63,plain,(
% 11.40/1.98    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f24])).
% 11.40/1.98  
% 11.40/1.98  fof(f13,axiom,(
% 11.40/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f29,plain,(
% 11.40/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.40/1.98    inference(ennf_transformation,[],[f13])).
% 11.40/1.98  
% 11.40/1.98  fof(f30,plain,(
% 11.40/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.40/1.98    inference(flattening,[],[f29])).
% 11.40/1.98  
% 11.40/1.98  fof(f38,plain,(
% 11.40/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.40/1.98    inference(nnf_transformation,[],[f30])).
% 11.40/1.98  
% 11.40/1.98  fof(f69,plain,(
% 11.40/1.98    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f38])).
% 11.40/1.98  
% 11.40/1.98  fof(f92,plain,(
% 11.40/1.98    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.40/1.98    inference(equality_resolution,[],[f69])).
% 11.40/1.98  
% 11.40/1.98  fof(f67,plain,(
% 11.40/1.98    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f37])).
% 11.40/1.98  
% 11.40/1.98  fof(f90,plain,(
% 11.40/1.98    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.40/1.98    inference(equality_resolution,[],[f67])).
% 11.40/1.98  
% 11.40/1.98  fof(f68,plain,(
% 11.40/1.98    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f38])).
% 11.40/1.98  
% 11.40/1.98  fof(f93,plain,(
% 11.40/1.98    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.40/1.98    inference(equality_resolution,[],[f68])).
% 11.40/1.98  
% 11.40/1.98  fof(f47,plain,(
% 11.40/1.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.40/1.98    inference(cnf_transformation,[],[f34])).
% 11.40/1.98  
% 11.40/1.98  fof(f83,plain,(
% 11.40/1.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.40/1.98    inference(equality_resolution,[],[f47])).
% 11.40/1.98  
% 11.40/1.98  fof(f51,plain,(
% 11.40/1.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f35])).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3,plain,
% 11.40/1.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.40/1.98      inference(cnf_transformation,[],[f49]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2432,plain,
% 11.40/1.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7,plain,
% 11.40/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.40/1.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.40/1.98      inference(cnf_transformation,[],[f53]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2428,plain,
% 11.40/1.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.40/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3369,plain,
% 11.40/1.98      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2432,c_2428]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_10,plain,
% 11.40/1.98      ( v1_funct_2(X0,k1_xboole_0,X1)
% 11.40/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.40/1.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 11.40/1.98      inference(cnf_transformation,[],[f88]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2425,plain,
% 11.40/1.98      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 11.40/1.98      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 11.40/1.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4821,plain,
% 11.40/1.98      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 11.40/1.98      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 11.40/1.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_3369,c_2425]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_6,plain,
% 11.40/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.40/1.98      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 11.40/1.98      inference(cnf_transformation,[],[f52]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2429,plain,
% 11.40/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.40/1.98      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4208,plain,
% 11.40/1.98      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
% 11.40/1.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_3369,c_2429]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_6915,plain,
% 11.40/1.98      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2432,c_4208]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5,plain,
% 11.40/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.40/1.98      inference(cnf_transformation,[],[f50]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2430,plain,
% 11.40/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.40/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_6943,plain,
% 11.40/1.98      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_6915,c_2430]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2860,plain,
% 11.40/1.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2432,c_2430]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_0,plain,
% 11.40/1.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.40/1.98      inference(cnf_transformation,[],[f48]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2434,plain,
% 11.40/1.98      ( X0 = X1
% 11.40/1.98      | r1_tarski(X0,X1) != iProver_top
% 11.40/1.98      | r1_tarski(X1,X0) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3944,plain,
% 11.40/1.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2860,c_2434]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_6989,plain,
% 11.40/1.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_6943,c_3944]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_11137,plain,
% 11.40/1.98      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 11.40/1.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 11.40/1.98      inference(global_propositional_subsumption,[status(thm)],[c_4821,c_6989]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_11143,plain,
% 11.40/1.98      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2432,c_11137]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_30,negated_conjecture,
% 11.40/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 11.40/1.98      inference(cnf_transformation,[],[f76]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2406,plain,
% 11.40/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_26,negated_conjecture,
% 11.40/1.98      ( sK2 = sK3 ),
% 11.40/1.98      inference(cnf_transformation,[],[f80]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2437,plain,
% 11.40/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 11.40/1.98      inference(light_normalisation,[status(thm)],[c_2406,c_26]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_13,plain,
% 11.40/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 11.40/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.40/1.98      | k1_relset_1(X1,X2,X0) = X1
% 11.40/1.98      | k1_xboole_0 = X2 ),
% 11.40/1.98      inference(cnf_transformation,[],[f54]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2422,plain,
% 11.40/1.98      ( k1_relset_1(X0,X1,X2) = X0
% 11.40/1.98      | k1_xboole_0 = X1
% 11.40/1.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.40/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5288,plain,
% 11.40/1.98      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = u1_struct_0(sK0)
% 11.40/1.98      | u1_struct_0(sK1) = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2437,c_2422]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3372,plain,
% 11.40/1.98      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2437,c_2428]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5289,plain,
% 11.40/1.98      ( u1_struct_0(sK1) = k1_xboole_0
% 11.40/1.98      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 11.40/1.98      inference(light_normalisation,[status(thm)],[c_5288,c_3372]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_31,negated_conjecture,
% 11.40/1.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 11.40/1.98      inference(cnf_transformation,[],[f75]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2405,plain,
% 11.40/1.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2436,plain,
% 11.40/1.98      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 11.40/1.98      inference(light_normalisation,[status(thm)],[c_2405,c_26]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5349,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3) | u1_struct_0(sK1) = k1_xboole_0 ),
% 11.40/1.98      inference(global_propositional_subsumption,[status(thm)],[c_5289,c_2436]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5350,plain,
% 11.40/1.98      ( u1_struct_0(sK1) = k1_xboole_0 | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 11.40/1.98      inference(renaming,[status(thm)],[c_5349]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5379,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_5350,c_2437]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_9,plain,
% 11.40/1.98      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 11.40/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 11.40/1.98      | k1_xboole_0 = X1
% 11.40/1.98      | k1_xboole_0 = X0 ),
% 11.40/1.98      inference(cnf_transformation,[],[f87]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2426,plain,
% 11.40/1.98      ( k1_xboole_0 = X0
% 11.40/1.98      | k1_xboole_0 = X1
% 11.40/1.98      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 11.40/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5486,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_5379,c_2426]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5380,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_5350,c_2436]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_6118,plain,
% 11.40/1.98      ( sK3 = k1_xboole_0
% 11.40/1.98      | u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 11.40/1.98      inference(global_propositional_subsumption,[status(thm)],[c_5486,c_5380]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_6119,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(renaming,[status(thm)],[c_6118]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_27,negated_conjecture,
% 11.40/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
% 11.40/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2409,plain,
% 11.40/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5287,plain,
% 11.40/1.98      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2409,c_2422]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3371,plain,
% 11.40/1.98      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2409,c_2428]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5290,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 11.40/1.98      inference(light_normalisation,[status(thm)],[c_5287,c_3371]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_28,negated_conjecture,
% 11.40/1.98      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
% 11.40/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5295,plain,
% 11.40/1.98      ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 11.40/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_5290]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7106,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0 ),
% 11.40/1.98      inference(global_propositional_subsumption,
% 11.40/1.98                [status(thm)],
% 11.40/1.98                [c_5290,c_28,c_5295]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7107,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 11.40/1.98      inference(renaming,[status(thm)],[c_7106]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7144,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_7107,c_2409]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7380,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_7144,c_2426]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2408,plain,
% 11.40/1.98      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7145,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_7107,c_2408]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7727,plain,
% 11.40/1.98      ( sK3 = k1_xboole_0
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 11.40/1.98      inference(global_propositional_subsumption,[status(thm)],[c_7380,c_7145]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7728,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(renaming,[status(thm)],[c_7727]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7729,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
% 11.40/1.98      | u1_struct_0(g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 11.40/1.98      | u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_6119,c_7728]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7778,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_7728,c_2408]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7777,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_7728,c_2409]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_21,plain,
% 11.40/1.98      ( ~ v5_pre_topc(X0,X1,X2)
% 11.40/1.98      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 11.40/1.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.40/1.98      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 11.40/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.40/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 11.40/1.98      | ~ v1_funct_1(X0)
% 11.40/1.98      | ~ v2_pre_topc(X1)
% 11.40/1.98      | ~ v2_pre_topc(X2)
% 11.40/1.98      | ~ l1_pre_topc(X1)
% 11.40/1.98      | ~ l1_pre_topc(X2) ),
% 11.40/1.98      inference(cnf_transformation,[],[f91]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2414,plain,
% 11.40/1.98      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 11.40/1.98      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 11.40/1.98      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 11.40/1.98      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 11.40/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 11.40/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 11.40/1.98      | v1_funct_1(X0) != iProver_top
% 11.40/1.98      | v2_pre_topc(X1) != iProver_top
% 11.40/1.98      | v2_pre_topc(X2) != iProver_top
% 11.40/1.98      | l1_pre_topc(X1) != iProver_top
% 11.40/1.98      | l1_pre_topc(X2) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4697,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 11.40/1.98      | v1_funct_1(sK3) != iProver_top
% 11.40/1.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 11.40/1.98      | v2_pre_topc(sK0) != iProver_top
% 11.40/1.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 11.40/1.98      | l1_pre_topc(sK0) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2409,c_2414]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_36,negated_conjecture,
% 11.40/1.98      ( v2_pre_topc(sK0) ),
% 11.40/1.98      inference(cnf_transformation,[],[f70]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_37,plain,
% 11.40/1.98      ( v2_pre_topc(sK0) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_35,negated_conjecture,
% 11.40/1.98      ( l1_pre_topc(sK0) ),
% 11.40/1.98      inference(cnf_transformation,[],[f71]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_38,plain,
% 11.40/1.98      ( l1_pre_topc(sK0) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_34,negated_conjecture,
% 11.40/1.98      ( v2_pre_topc(sK1) ),
% 11.40/1.98      inference(cnf_transformation,[],[f72]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_39,plain,
% 11.40/1.98      ( v2_pre_topc(sK1) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_33,negated_conjecture,
% 11.40/1.98      ( l1_pre_topc(sK1) ),
% 11.40/1.98      inference(cnf_transformation,[],[f73]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_40,plain,
% 11.40/1.98      ( l1_pre_topc(sK1) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_29,negated_conjecture,
% 11.40/1.98      ( v1_funct_1(sK3) ),
% 11.40/1.98      inference(cnf_transformation,[],[f77]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_44,plain,
% 11.40/1.98      ( v1_funct_1(sK3) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_45,plain,
% 11.40/1.98      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_46,plain,
% 11.40/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_25,negated_conjecture,
% 11.40/1.98      ( v5_pre_topc(sK2,sK0,sK1)
% 11.40/1.98      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 11.40/1.98      inference(cnf_transformation,[],[f81]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2410,plain,
% 11.40/1.98      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2438,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
% 11.40/1.98      inference(light_normalisation,[status(thm)],[c_2410,c_26]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_24,negated_conjecture,
% 11.40/1.98      ( ~ v5_pre_topc(sK2,sK0,sK1)
% 11.40/1.98      | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 11.40/1.98      inference(cnf_transformation,[],[f82]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2411,plain,
% 11.40/1.98      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2439,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
% 11.40/1.98      inference(light_normalisation,[status(thm)],[c_2411,c_26]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_18,plain,
% 11.40/1.98      ( ~ v2_pre_topc(X0)
% 11.40/1.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 11.40/1.98      | ~ l1_pre_topc(X0) ),
% 11.40/1.98      inference(cnf_transformation,[],[f65]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2579,plain,
% 11.40/1.98      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 11.40/1.98      | ~ v2_pre_topc(sK1)
% 11.40/1.98      | ~ l1_pre_topc(sK1) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_18]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2580,plain,
% 11.40/1.98      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 11.40/1.98      | v2_pre_topc(sK1) != iProver_top
% 11.40/1.98      | l1_pre_topc(sK1) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_2579]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_15,plain,
% 11.40/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.40/1.98      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 11.40/1.98      inference(cnf_transformation,[],[f62]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2691,plain,
% 11.40/1.98      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 11.40/1.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_15]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2692,plain,
% 11.40/1.98      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 11.40/1.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_2691]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_17,plain,
% 11.40/1.98      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 11.40/1.98      | ~ l1_pre_topc(X0) ),
% 11.40/1.98      inference(cnf_transformation,[],[f63]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2850,plain,
% 11.40/1.98      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 11.40/1.98      | ~ l1_pre_topc(sK1) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_17]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2851,plain,
% 11.40/1.98      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 11.40/1.98      | l1_pre_topc(sK1) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_2850]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_22,plain,
% 11.40/1.98      ( v5_pre_topc(X0,X1,X2)
% 11.40/1.98      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 11.40/1.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.40/1.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 11.40/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.40/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 11.40/1.98      | ~ v1_funct_1(X0)
% 11.40/1.98      | ~ v2_pre_topc(X1)
% 11.40/1.98      | ~ v2_pre_topc(X2)
% 11.40/1.98      | ~ l1_pre_topc(X1)
% 11.40/1.98      | ~ l1_pre_topc(X2) ),
% 11.40/1.98      inference(cnf_transformation,[],[f92]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2734,plain,
% 11.40/1.98      ( ~ v5_pre_topc(sK3,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 11.40/1.98      | v5_pre_topc(sK3,X0,sK1)
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 11.40/1.98      | ~ v1_funct_1(sK3)
% 11.40/1.98      | ~ v2_pre_topc(X0)
% 11.40/1.98      | ~ v2_pre_topc(sK1)
% 11.40/1.98      | ~ l1_pre_topc(X0)
% 11.40/1.98      | ~ l1_pre_topc(sK1) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_22]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3221,plain,
% 11.40/1.98      ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 11.40/1.98      | v5_pre_topc(sK3,sK0,sK1)
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.40/1.98      | ~ v1_funct_1(sK3)
% 11.40/1.98      | ~ v2_pre_topc(sK1)
% 11.40/1.98      | ~ v2_pre_topc(sK0)
% 11.40/1.98      | ~ l1_pre_topc(sK1)
% 11.40/1.98      | ~ l1_pre_topc(sK0) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_2734]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3222,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_1(sK3) != iProver_top
% 11.40/1.98      | v2_pre_topc(sK1) != iProver_top
% 11.40/1.98      | v2_pre_topc(sK0) != iProver_top
% 11.40/1.98      | l1_pre_topc(sK1) != iProver_top
% 11.40/1.98      | l1_pre_topc(sK0) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_3221]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_20,plain,
% 11.40/1.98      ( v5_pre_topc(X0,X1,X2)
% 11.40/1.98      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 11.40/1.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.40/1.98      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 11.40/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.40/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 11.40/1.98      | ~ v1_funct_1(X0)
% 11.40/1.98      | ~ v2_pre_topc(X1)
% 11.40/1.98      | ~ v2_pre_topc(X2)
% 11.40/1.98      | ~ l1_pre_topc(X1)
% 11.40/1.98      | ~ l1_pre_topc(X2) ),
% 11.40/1.98      inference(cnf_transformation,[],[f90]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2973,plain,
% 11.40/1.98      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
% 11.40/1.98      | v5_pre_topc(sK3,sK0,X0)
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 11.40/1.98      | ~ v1_funct_1(sK3)
% 11.40/1.98      | ~ v2_pre_topc(X0)
% 11.40/1.98      | ~ v2_pre_topc(sK0)
% 11.40/1.98      | ~ l1_pre_topc(X0)
% 11.40/1.98      | ~ l1_pre_topc(sK0) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_20]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3254,plain,
% 11.40/1.98      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 11.40/1.98      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 11.40/1.98      | ~ v1_funct_1(sK3)
% 11.40/1.98      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 11.40/1.98      | ~ v2_pre_topc(sK0)
% 11.40/1.98      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 11.40/1.98      | ~ l1_pre_topc(sK0) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_2973]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3255,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 11.40/1.98      | v1_funct_1(sK3) != iProver_top
% 11.40/1.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 11.40/1.98      | v2_pre_topc(sK0) != iProver_top
% 11.40/1.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 11.40/1.98      | l1_pre_topc(sK0) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_3254]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_23,plain,
% 11.40/1.98      ( ~ v5_pre_topc(X0,X1,X2)
% 11.40/1.98      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 11.40/1.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.40/1.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 11.40/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.40/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 11.40/1.98      | ~ v1_funct_1(X0)
% 11.40/1.98      | ~ v2_pre_topc(X1)
% 11.40/1.98      | ~ v2_pre_topc(X2)
% 11.40/1.98      | ~ l1_pre_topc(X1)
% 11.40/1.98      | ~ l1_pre_topc(X2) ),
% 11.40/1.98      inference(cnf_transformation,[],[f93]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3170,plain,
% 11.40/1.98      ( ~ v5_pre_topc(sK3,sK0,X0)
% 11.40/1.98      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
% 11.40/1.98      | ~ v1_funct_1(sK3)
% 11.40/1.98      | ~ v2_pre_topc(X0)
% 11.40/1.98      | ~ v2_pre_topc(sK0)
% 11.40/1.98      | ~ l1_pre_topc(X0)
% 11.40/1.98      | ~ l1_pre_topc(sK0) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_23]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4676,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 11.40/1.98      | ~ v5_pre_topc(sK3,sK0,sK1)
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.40/1.98      | ~ v1_funct_1(sK3)
% 11.40/1.98      | ~ v2_pre_topc(sK1)
% 11.40/1.98      | ~ v2_pre_topc(sK0)
% 11.40/1.98      | ~ l1_pre_topc(sK1)
% 11.40/1.98      | ~ l1_pre_topc(sK0) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_3170]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4677,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_1(sK3) != iProver_top
% 11.40/1.98      | v2_pre_topc(sK1) != iProver_top
% 11.40/1.98      | v2_pre_topc(sK0) != iProver_top
% 11.40/1.98      | l1_pre_topc(sK1) != iProver_top
% 11.40/1.98      | l1_pre_topc(sK0) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_4676]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4826,plain,
% 11.40/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 11.40/1.98      inference(global_propositional_subsumption,
% 11.40/1.98                [status(thm)],
% 11.40/1.98                [c_4697,c_37,c_38,c_39,c_40,c_44,c_45,c_46,c_2438,c_2439,
% 11.40/1.98                 c_2437,c_2436,c_2580,c_2692,c_2851,c_3222,c_3255,c_4677]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4827,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 11.40/1.98      inference(renaming,[status(thm)],[c_4826]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4830,plain,
% 11.40/1.98      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 11.40/1.98      inference(global_propositional_subsumption,
% 11.40/1.98                [status(thm)],
% 11.40/1.98                [c_4827,c_37,c_38,c_39,c_40,c_44,c_45,c_46,c_2438,c_2437,
% 11.40/1.98                 c_2436,c_2580,c_2692,c_2851,c_3255,c_4677]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_6153,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_6119,c_4830]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_8805,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
% 11.40/1.98      | u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_7777,c_6153]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_9216,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
% 11.40/1.98      | u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_6119,c_8805]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_14296,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
% 11.40/1.98      | u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(global_propositional_subsumption,
% 11.40/1.98                [status(thm)],
% 11.40/1.98                [c_7729,c_7778,c_9216]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_14389,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_14296,c_2409]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4211,plain,
% 11.40/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.40/1.98      | r1_tarski(k1_relset_1(X1,X2,X0),X1) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2429,c_2430]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_14997,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | r1_tarski(k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3),k1_xboole_0) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_14389,c_4211]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_15808,plain,
% 11.40/1.98      ( k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_xboole_0
% 11.40/1.98      | u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_14997,c_3944]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_14387,plain,
% 11.40/1.98      ( k1_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3)
% 11.40/1.98      | u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_14296,c_3371]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_17926,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | k1_relat_1(sK3) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_15808,c_14387]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_18037,plain,
% 11.40/1.98      ( k1_relat_1(sK3) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_17926,c_2437]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_18573,plain,
% 11.40/1.98      ( k1_relat_1(sK3) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | r1_tarski(k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3),k1_xboole_0) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_18037,c_4211]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_19321,plain,
% 11.40/1.98      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
% 11.40/1.98      | k1_relat_1(sK3) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_18573,c_3944]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_18030,plain,
% 11.40/1.98      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_relat_1(sK3)
% 11.40/1.98      | k1_relat_1(sK3) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_17926,c_3372]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_20686,plain,
% 11.40/1.98      ( k1_relat_1(sK3) = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_19321,c_18030]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_20744,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_20686,c_7778]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2636,plain,
% 11.40/1.98      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_0]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2761,plain,
% 11.40/1.98      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_2636]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f83]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2998,plain,
% 11.40/1.98      ( r1_tarski(sK3,sK3) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_1]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_1594,plain,
% 11.40/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 11.40/1.98      | v1_funct_2(X3,X4,X5)
% 11.40/1.98      | X3 != X0
% 11.40/1.98      | X4 != X1
% 11.40/1.98      | X5 != X2 ),
% 11.40/1.98      theory(equality) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4282,plain,
% 11.40/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != X2
% 11.40/1.98      | u1_struct_0(sK0) != X1
% 11.40/1.98      | sK3 != X0 ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_1594]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7525,plain,
% 11.40/1.98      ( ~ v1_funct_2(sK3,X0,X1)
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != X1
% 11.40/1.98      | u1_struct_0(sK0) != X0
% 11.40/1.98      | sK3 != sK3 ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_4282]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_11863,plain,
% 11.40/1.98      ( ~ v1_funct_2(sK3,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 11.40/1.98      | u1_struct_0(sK0) != X0
% 11.40/1.98      | sK3 != sK3 ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_7525]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_11864,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 11.40/1.98      | u1_struct_0(sK0) != X0
% 11.40/1.98      | sK3 != sK3
% 11.40/1.98      | v1_funct_2(sK3,X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_11863]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_11866,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 11.40/1.98      | u1_struct_0(sK0) != k1_xboole_0
% 11.40/1.98      | sK3 != sK3
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top
% 11.40/1.98      | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_11864]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_1588,plain,( X0 = X0 ),theory(equality) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_19878,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_1588]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_6168,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_6119,c_2436]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_20756,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_20686,c_6168]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4394,plain,
% 11.40/1.98      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_1588]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4267,plain,
% 11.40/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != X1
% 11.40/1.98      | u1_struct_0(sK1) != X2
% 11.40/1.98      | sK3 != X0 ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_1594]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7492,plain,
% 11.40/1.98      ( ~ v1_funct_2(sK3,X0,X1)
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != X0
% 11.40/1.98      | u1_struct_0(sK1) != X1
% 11.40/1.98      | sK3 != sK3 ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_4267]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_11827,plain,
% 11.40/1.98      ( ~ v1_funct_2(sK3,X0,u1_struct_0(sK1))
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != X0
% 11.40/1.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 11.40/1.98      | sK3 != sK3 ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_7492]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_11828,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != X0
% 11.40/1.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 11.40/1.98      | sK3 != sK3
% 11.40/1.98      | v1_funct_2(sK3,X0,u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_11827]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_11830,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_xboole_0
% 11.40/1.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 11.40/1.98      | sK3 != sK3
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) = iProver_top
% 11.40/1.98      | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_11828]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4,plain,
% 11.40/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.40/1.98      inference(cnf_transformation,[],[f51]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2431,plain,
% 11.40/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.40/1.98      | r1_tarski(X0,X1) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2413,plain,
% 11.40/1.98      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 11.40/1.98      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 11.40/1.98      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 11.40/1.98      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 11.40/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 11.40/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 11.40/1.98      | v1_funct_1(X0) != iProver_top
% 11.40/1.98      | v2_pre_topc(X1) != iProver_top
% 11.40/1.98      | v2_pre_topc(X2) != iProver_top
% 11.40/1.98      | l1_pre_topc(X1) != iProver_top
% 11.40/1.98      | l1_pre_topc(X2) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3936,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_1(sK3) != iProver_top
% 11.40/1.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 11.40/1.98      | v2_pre_topc(sK1) != iProver_top
% 11.40/1.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 11.40/1.98      | l1_pre_topc(sK1) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2409,c_2413]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2564,plain,
% 11.40/1.98      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 11.40/1.98      | ~ v2_pre_topc(sK0)
% 11.40/1.98      | ~ l1_pre_topc(sK0) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_18]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2565,plain,
% 11.40/1.98      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 11.40/1.98      | v2_pre_topc(sK0) != iProver_top
% 11.40/1.98      | l1_pre_topc(sK0) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_2564]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2679,plain,
% 11.40/1.98      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 11.40/1.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_15]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2680,plain,
% 11.40/1.98      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 11.40/1.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_2679]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2839,plain,
% 11.40/1.98      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 11.40/1.98      | ~ l1_pre_topc(sK0) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_17]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2840,plain,
% 11.40/1.98      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 11.40/1.98      | l1_pre_topc(sK0) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_2839]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2412,plain,
% 11.40/1.98      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 11.40/1.98      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 11.40/1.98      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 11.40/1.98      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 11.40/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 11.40/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 11.40/1.98      | v1_funct_1(X0) != iProver_top
% 11.40/1.98      | v2_pre_topc(X1) != iProver_top
% 11.40/1.98      | v2_pre_topc(X2) != iProver_top
% 11.40/1.98      | l1_pre_topc(X1) != iProver_top
% 11.40/1.98      | l1_pre_topc(X2) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3180,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_1(sK3) != iProver_top
% 11.40/1.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 11.40/1.98      | v2_pre_topc(sK1) != iProver_top
% 11.40/1.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 11.40/1.98      | l1_pre_topc(sK1) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2409,c_2412]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3245,plain,
% 11.40/1.98      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 11.40/1.98      | v5_pre_topc(sK3,sK0,sK1)
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.40/1.98      | ~ v1_funct_1(sK3)
% 11.40/1.98      | ~ v2_pre_topc(sK1)
% 11.40/1.98      | ~ v2_pre_topc(sK0)
% 11.40/1.98      | ~ l1_pre_topc(sK1)
% 11.40/1.98      | ~ l1_pre_topc(sK0) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_2973]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3246,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_1(sK3) != iProver_top
% 11.40/1.98      | v2_pre_topc(sK1) != iProver_top
% 11.40/1.98      | v2_pre_topc(sK0) != iProver_top
% 11.40/1.98      | l1_pre_topc(sK1) != iProver_top
% 11.40/1.98      | l1_pre_topc(sK0) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_3245]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3564,plain,
% 11.40/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
% 11.40/1.98      inference(global_propositional_subsumption,
% 11.40/1.98                [status(thm)],
% 11.40/1.98                [c_3180,c_37,c_38,c_39,c_40,c_44,c_45,c_2439,c_2437,c_2436,
% 11.40/1.98                 c_2565,c_2680,c_2840,c_3246]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3565,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 11.40/1.98      inference(renaming,[status(thm)],[c_3564]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4341,plain,
% 11.40/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 11.40/1.98      inference(global_propositional_subsumption,
% 11.40/1.98                [status(thm)],
% 11.40/1.98                [c_3936,c_37,c_38,c_39,c_40,c_44,c_45,c_2439,c_2437,c_2436,
% 11.40/1.98                 c_2565,c_2680,c_2840,c_3180,c_3246]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4342,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 11.40/1.98      inference(renaming,[status(thm)],[c_4341]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5368,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_5350,c_4342]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4345,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2438,c_4342]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_3154,plain,
% 11.40/1.98      ( ~ v5_pre_topc(sK3,X0,sK1)
% 11.40/1.98      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))))
% 11.40/1.98      | ~ v1_funct_1(sK3)
% 11.40/1.98      | ~ v2_pre_topc(X0)
% 11.40/1.98      | ~ v2_pre_topc(sK1)
% 11.40/1.98      | ~ l1_pre_topc(X0)
% 11.40/1.98      | ~ l1_pre_topc(sK1) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_21]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4662,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 11.40/1.98      | ~ v5_pre_topc(sK3,sK0,sK1)
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 11.40/1.98      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 11.40/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.40/1.98      | ~ v1_funct_1(sK3)
% 11.40/1.98      | ~ v2_pre_topc(sK1)
% 11.40/1.98      | ~ v2_pre_topc(sK0)
% 11.40/1.98      | ~ l1_pre_topc(sK1)
% 11.40/1.98      | ~ l1_pre_topc(sK0) ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_3154]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4663,plain,
% 11.40/1.98      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 11.40/1.98      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.40/1.98      | v1_funct_1(sK3) != iProver_top
% 11.40/1.98      | v2_pre_topc(sK1) != iProver_top
% 11.40/1.98      | v2_pre_topc(sK0) != iProver_top
% 11.40/1.98      | l1_pre_topc(sK1) != iProver_top
% 11.40/1.98      | l1_pre_topc(sK0) != iProver_top ),
% 11.40/1.98      inference(predicate_to_equality,[status(thm)],[c_4662]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5842,plain,
% 11.40/1.98      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 11.40/1.98      inference(global_propositional_subsumption,
% 11.40/1.98                [status(thm)],
% 11.40/1.98                [c_5368,c_37,c_38,c_39,c_40,c_44,c_2437,c_2436,c_3565,c_4345,
% 11.40/1.98                 c_4663]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5846,plain,
% 11.40/1.98      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2431,c_5842]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_14366,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_14296,c_5846]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2861,plain,
% 11.40/1.98      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2437,c_2430]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_6162,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_6119,c_2861]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_20749,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_20686,c_6162]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_20853,plain,
% 11.40/1.98      ( sK3 = k1_xboole_0 | u1_struct_0(sK0) = k1_xboole_0 ),
% 11.40/1.98      inference(global_propositional_subsumption,
% 11.40/1.98                [status(thm)],
% 11.40/1.98                [c_20756,c_2761,c_2998,c_4394,c_11830,c_14296,c_14366,c_20749]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_20854,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(renaming,[status(thm)],[c_20853]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_20951,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_20854,c_5379]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_5370,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_5350,c_3565]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7381,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 11.40/1.98      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_7144,c_5370]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7140,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_7107,c_4830]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_7465,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_7107,c_7140]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_9226,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 11.40/1.98      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 11.40/1.98      inference(global_propositional_subsumption,
% 11.40/1.98                [status(thm)],
% 11.40/1.98                [c_7381,c_5379,c_5380,c_7465]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_2947,plain,
% 11.40/1.98      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2409,c_2430]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_9280,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_9226,c_2947]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_20728,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_20686,c_9280]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_9282,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_9226,c_2408]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_20733,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_20686,c_9282]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_4834,plain,
% 11.40/1.98      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2431,c_4830]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_20958,plain,
% 11.40/1.98      ( sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_20854,c_4834]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_22291,plain,
% 11.40/1.98      ( sK3 = k1_xboole_0 | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 11.40/1.98      inference(global_propositional_subsumption,
% 11.40/1.98                [status(thm)],
% 11.40/1.98                [c_20951,c_2761,c_2998,c_4394,c_11830,c_11866,c_14296,c_14366,
% 11.40/1.98                 c_19878,c_20728,c_20733,c_20749,c_20756,c_20958]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_22292,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3) | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(renaming,[status(thm)],[c_22291]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_22399,plain,
% 11.40/1.98      ( sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_22292,c_4830]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_24102,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_7777,c_22399]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_25446,plain,
% 11.40/1.98      ( sK3 = k1_xboole_0
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0 ),
% 11.40/1.98      inference(global_propositional_subsumption,
% 11.40/1.98                [status(thm)],
% 11.40/1.98                [c_20744,c_2761,c_2998,c_4394,c_11830,c_11866,c_14296,c_14366,
% 11.40/1.98                 c_19878,c_20749,c_20756,c_24102]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_25447,plain,
% 11.40/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
% 11.40/1.98      | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(renaming,[status(thm)],[c_25446]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_25553,plain,
% 11.40/1.98      ( sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_25447,c_2408]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_11829,plain,
% 11.40/1.98      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 11.40/1.98      | ~ v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1))
% 11.40/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_xboole_0
% 11.40/1.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 11.40/1.98      | sK3 != sK3 ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_11827]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_20967,plain,
% 11.40/1.98      ( sK3 = k1_xboole_0
% 11.40/1.98      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_20854,c_2861]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_21130,plain,
% 11.40/1.98      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 11.40/1.98      | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_20967]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_20973,plain,
% 11.40/1.98      ( sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) = iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_20854,c_2436]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_21136,plain,
% 11.40/1.98      ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_20973]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_25530,plain,
% 11.40/1.98      ( sK3 = k1_xboole_0
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_25447,c_5846]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_25704,plain,
% 11.40/1.98      ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 11.40/1.98      | ~ r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 11.40/1.98      | sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_25530]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_25716,plain,
% 11.40/1.98      ( sK3 = k1_xboole_0 ),
% 11.40/1.98      inference(global_propositional_subsumption,
% 11.40/1.98                [status(thm)],
% 11.40/1.98                [c_25553,c_2761,c_2998,c_4394,c_11829,c_21130,c_21136,c_25447,
% 11.40/1.98                 c_25704]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_10727,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_9226,c_5846]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_10795,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_9226,c_10727]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_10861,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
% 11.40/1.98      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_5350,c_10795]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_10865,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 11.40/1.98      | v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 11.40/1.98      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_5350,c_10861]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_25763,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
% 11.40/1.98      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 11.40/1.98      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)) != iProver_top ),
% 11.40/1.98      inference(demodulation,[status(thm)],[c_25716,c_10865]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_25891,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 11.40/1.98      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 11.40/1.98      inference(light_normalisation,[status(thm)],[c_25763,c_6989]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_11146,plain,
% 11.40/1.98      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.40/1.98      inference(instantiation,[status(thm)],[c_11143]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_29094,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_xboole_0
% 11.40/1.98      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 11.40/1.98      inference(global_propositional_subsumption,
% 11.40/1.98                [status(thm)],
% 11.40/1.98                [c_25891,c_11146]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_29098,plain,
% 11.40/1.98      ( u1_struct_0(sK0) = k1_xboole_0 ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2860,c_29094]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_25811,plain,
% 11.40/1.98      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 11.40/1.98      | r1_tarski(k1_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
% 11.40/1.98      inference(demodulation,[status(thm)],[c_25716,c_4834]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_26884,plain,
% 11.40/1.98      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_2860,c_25811]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_33877,plain,
% 11.40/1.98      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 11.40/1.98      inference(demodulation,[status(thm)],[c_29098,c_26884]) ).
% 11.40/1.98  
% 11.40/1.98  cnf(c_42442,plain,
% 11.40/1.98      ( $false ),
% 11.40/1.98      inference(superposition,[status(thm)],[c_11143,c_33877]) ).
% 11.40/1.98  
% 11.40/1.98  
% 11.40/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.40/1.98  
% 11.40/1.98  ------                               Statistics
% 11.40/1.98  
% 11.40/1.98  ------ General
% 11.40/1.98  
% 11.40/1.98  abstr_ref_over_cycles:                  0
% 11.40/1.98  abstr_ref_under_cycles:                 0
% 11.40/1.98  gc_basic_clause_elim:                   0
% 11.40/1.98  forced_gc_time:                         0
% 11.40/1.98  parsing_time:                           0.009
% 11.40/1.98  unif_index_cands_time:                  0.
% 11.40/1.98  unif_index_add_time:                    0.
% 11.40/1.98  orderings_time:                         0.
% 11.40/1.98  out_proof_time:                         0.025
% 11.40/1.98  total_time:                             1.364
% 11.40/1.98  num_of_symbols:                         51
% 11.40/1.98  num_of_terms:                           30378
% 11.40/1.98  
% 11.40/1.98  ------ Preprocessing
% 11.40/1.98  
% 11.40/1.98  num_of_splits:                          0
% 11.40/1.98  num_of_split_atoms:                     0
% 11.40/1.98  num_of_reused_defs:                     0
% 11.40/1.98  num_eq_ax_congr_red:                    15
% 11.40/1.98  num_of_sem_filtered_clauses:            1
% 11.40/1.98  num_of_subtypes:                        0
% 11.40/1.98  monotx_restored_types:                  0
% 11.40/1.98  sat_num_of_epr_types:                   0
% 11.40/1.98  sat_num_of_non_cyclic_types:            0
% 11.40/1.98  sat_guarded_non_collapsed_types:        0
% 11.40/1.98  num_pure_diseq_elim:                    0
% 11.40/1.98  simp_replaced_by:                       0
% 11.40/1.98  res_preprocessed:                       175
% 11.40/1.98  prep_upred:                             0
% 11.40/1.98  prep_unflattend:                        20
% 11.40/1.98  smt_new_axioms:                         0
% 11.40/1.98  pred_elim_cands:                        8
% 11.40/1.98  pred_elim:                              0
% 11.40/1.98  pred_elim_cl:                           0
% 11.40/1.98  pred_elim_cycles:                       4
% 11.40/1.98  merged_defs:                            16
% 11.40/1.98  merged_defs_ncl:                        0
% 11.40/1.98  bin_hyper_res:                          16
% 11.40/1.98  prep_cycles:                            4
% 11.40/1.98  pred_elim_time:                         0.021
% 11.40/1.98  splitting_time:                         0.
% 11.40/1.98  sem_filter_time:                        0.
% 11.40/1.98  monotx_time:                            0.001
% 11.40/1.98  subtype_inf_time:                       0.
% 11.40/1.98  
% 11.40/1.98  ------ Problem properties
% 11.40/1.98  
% 11.40/1.98  clauses:                                36
% 11.40/1.98  conjectures:                            13
% 11.40/1.98  epr:                                    9
% 11.40/1.98  horn:                                   31
% 11.40/1.98  ground:                                 13
% 11.40/1.98  unary:                                  13
% 11.40/1.98  binary:                                 9
% 11.40/1.98  lits:                                   108
% 11.40/1.98  lits_eq:                                13
% 11.40/1.98  fd_pure:                                0
% 11.40/1.98  fd_pseudo:                              0
% 11.40/1.98  fd_cond:                                3
% 11.40/1.98  fd_pseudo_cond:                         1
% 11.40/1.98  ac_symbols:                             0
% 11.40/1.98  
% 11.40/1.98  ------ Propositional Solver
% 11.40/1.98  
% 11.40/1.98  prop_solver_calls:                      35
% 11.40/1.98  prop_fast_solver_calls:                 6337
% 11.40/1.98  smt_solver_calls:                       0
% 11.40/1.98  smt_fast_solver_calls:                  0
% 11.40/1.98  prop_num_of_clauses:                    17365
% 11.40/1.98  prop_preprocess_simplified:             33439
% 11.40/1.98  prop_fo_subsumed:                       1192
% 11.40/1.98  prop_solver_time:                       0.
% 11.40/1.98  smt_solver_time:                        0.
% 11.40/1.98  smt_fast_solver_time:                   0.
% 11.40/1.98  prop_fast_solver_time:                  0.
% 11.40/1.98  prop_unsat_core_time:                   0.
% 11.40/1.98  
% 11.40/1.98  ------ QBF
% 11.40/1.98  
% 11.40/1.98  qbf_q_res:                              0
% 11.40/1.98  qbf_num_tautologies:                    0
% 11.40/1.98  qbf_prep_cycles:                        0
% 11.40/1.98  
% 11.40/1.98  ------ BMC1
% 11.40/1.98  
% 11.40/1.98  bmc1_current_bound:                     -1
% 11.40/1.98  bmc1_last_solved_bound:                 -1
% 11.40/1.98  bmc1_unsat_core_size:                   -1
% 11.40/1.98  bmc1_unsat_core_parents_size:           -1
% 11.40/1.98  bmc1_merge_next_fun:                    0
% 11.40/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.40/1.98  
% 11.40/1.98  ------ Instantiation
% 11.40/1.98  
% 11.40/1.98  inst_num_of_clauses:                    4205
% 11.40/1.98  inst_num_in_passive:                    2149
% 11.40/1.98  inst_num_in_active:                     1801
% 11.40/1.98  inst_num_in_unprocessed:                255
% 11.40/1.98  inst_num_of_loops:                      2180
% 11.40/1.98  inst_num_of_learning_restarts:          0
% 11.40/1.98  inst_num_moves_active_passive:          374
% 11.40/1.98  inst_lit_activity:                      0
% 11.40/1.98  inst_lit_activity_moves:                0
% 11.40/1.98  inst_num_tautologies:                   0
% 11.40/1.98  inst_num_prop_implied:                  0
% 11.40/1.98  inst_num_existing_simplified:           0
% 11.40/1.98  inst_num_eq_res_simplified:             0
% 11.40/1.98  inst_num_child_elim:                    0
% 11.40/1.98  inst_num_of_dismatching_blockings:      3505
% 11.40/1.98  inst_num_of_non_proper_insts:           5744
% 11.40/1.98  inst_num_of_duplicates:                 0
% 11.40/1.98  inst_inst_num_from_inst_to_res:         0
% 11.40/1.98  inst_dismatching_checking_time:         0.
% 11.40/1.98  
% 11.40/1.98  ------ Resolution
% 11.40/1.98  
% 11.40/1.98  res_num_of_clauses:                     0
% 11.40/1.98  res_num_in_passive:                     0
% 11.40/1.98  res_num_in_active:                      0
% 11.40/1.98  res_num_of_loops:                       179
% 11.40/1.98  res_forward_subset_subsumed:            334
% 11.40/1.98  res_backward_subset_subsumed:           2
% 11.40/1.98  res_forward_subsumed:                   0
% 11.40/1.98  res_backward_subsumed:                  0
% 11.40/1.98  res_forward_subsumption_resolution:     0
% 11.40/1.98  res_backward_subsumption_resolution:    0
% 11.40/1.98  res_clause_to_clause_subsumption:       3736
% 11.40/1.98  res_orphan_elimination:                 0
% 11.40/1.98  res_tautology_del:                      419
% 11.40/1.98  res_num_eq_res_simplified:              0
% 11.40/1.98  res_num_sel_changes:                    0
% 11.40/1.98  res_moves_from_active_to_pass:          0
% 11.40/1.98  
% 11.40/1.98  ------ Superposition
% 11.40/1.98  
% 11.40/1.98  sup_time_total:                         0.
% 11.40/1.98  sup_time_generating:                    0.
% 11.40/1.98  sup_time_sim_full:                      0.
% 11.40/1.98  sup_time_sim_immed:                     0.
% 11.40/1.98  
% 11.40/1.98  sup_num_of_clauses:                     375
% 11.40/1.98  sup_num_in_active:                      153
% 11.40/1.98  sup_num_in_passive:                     222
% 11.40/1.98  sup_num_of_loops:                       435
% 11.40/1.98  sup_fw_superposition:                   1070
% 11.40/1.98  sup_bw_superposition:                   1780
% 11.40/1.98  sup_immediate_simplified:               933
% 11.40/1.98  sup_given_eliminated:                   4
% 11.40/1.98  comparisons_done:                       0
% 11.40/1.98  comparisons_avoided:                    137
% 11.40/1.98  
% 11.40/1.98  ------ Simplifications
% 11.40/1.98  
% 11.40/1.98  
% 11.40/1.98  sim_fw_subset_subsumed:                 297
% 11.40/1.98  sim_bw_subset_subsumed:                 677
% 11.40/1.98  sim_fw_subsumed:                        117
% 11.40/1.98  sim_bw_subsumed:                        55
% 11.40/1.98  sim_fw_subsumption_res:                 0
% 11.40/1.98  sim_bw_subsumption_res:                 0
% 11.40/1.98  sim_tautology_del:                      287
% 11.40/1.98  sim_eq_tautology_del:                   148
% 11.40/1.98  sim_eq_res_simp:                        0
% 11.40/1.98  sim_fw_demodulated:                     213
% 11.40/1.98  sim_bw_demodulated:                     141
% 11.40/1.98  sim_light_normalised:                   522
% 11.40/1.98  sim_joinable_taut:                      0
% 11.40/1.98  sim_joinable_simp:                      0
% 11.40/1.98  sim_ac_normalised:                      0
% 11.40/1.98  sim_smt_subsumption:                    0
% 11.40/1.98  
%------------------------------------------------------------------------------
