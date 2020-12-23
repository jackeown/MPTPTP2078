%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:19 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  217 (1952 expanded)
%              Number of clauses        :  161 ( 633 expanded)
%              Number of leaves         :   20 ( 573 expanded)
%              Depth                    :   25
%              Number of atoms          :  972 (21038 expanded)
%              Number of equality atoms :  401 (2062 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                  & u1_struct_0(X0) = u1_struct_0(X1) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v5_pre_topc(X3,X1,X2)
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X3) )
                   => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v5_pre_topc(X3,X0,X2)
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                    & u1_struct_0(X0) = u1_struct_0(X1) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v5_pre_topc(X3,X1,X2)
                        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X3) )
                     => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                        & v5_pre_topc(X3,X0,X2)
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                        & v1_funct_1(X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                    & u1_struct_0(X0) = u1_struct_0(X1) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v5_pre_topc(X3,X1,X2)
                        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X3) )
                     => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                        & v5_pre_topc(X3,X0,X2)
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                        & v1_funct_1(X3) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    | ~ v5_pre_topc(X3,X0,X2)
                    | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    | ~ v1_funct_1(X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  & v5_pre_topc(X3,X1,X2)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    | ~ v5_pre_topc(X3,X0,X2)
                    | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    | ~ v1_funct_1(X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  & v5_pre_topc(X3,X1,X2)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
            | ~ v5_pre_topc(X3,X0,X2)
            | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
          & v5_pre_topc(X3,X1,X2)
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
          & v1_funct_1(X3) )
     => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
          | ~ v5_pre_topc(sK4,X0,X2)
          | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X2))
          | ~ v1_funct_1(sK4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & v5_pre_topc(sK4,X1,X2)
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                | ~ v5_pre_topc(X3,X0,X2)
                | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
              & v5_pre_topc(X3,X1,X2)
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
              & v1_funct_1(X3) )
          & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
              | ~ v5_pre_topc(X3,X0,sK3)
              | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK3))
              | ~ v1_funct_1(X3) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
            & v5_pre_topc(X3,X1,sK3)
            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK3))
            & v1_funct_1(X3) )
        & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
        & u1_struct_0(X0) = u1_struct_0(X1)
        & l1_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    | ~ v5_pre_topc(X3,X0,X2)
                    | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    | ~ v1_funct_1(X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  & v5_pre_topc(X3,X1,X2)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  | ~ v5_pre_topc(X3,X0,X2)
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
                & v5_pre_topc(X3,sK2,X2)
                & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
                & v1_funct_1(X3) )
            & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X0))
            & u1_struct_0(sK2) = u1_struct_0(X0)
            & l1_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      | ~ v5_pre_topc(X3,X0,X2)
                      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      | ~ v1_funct_1(X3) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v5_pre_topc(X3,X1,X2)
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                & u1_struct_0(X0) = u1_struct_0(X1)
                & l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
                    | ~ v5_pre_topc(X3,sK1,X2)
                    | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
                    | ~ v1_funct_1(X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  & v5_pre_topc(X3,X1,X2)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(sK1))
              & u1_struct_0(sK1) = u1_struct_0(X1)
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
      | ~ v5_pre_topc(sK4,sK1,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v5_pre_topc(sK4,sK2,sK3)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
    & u1_struct_0(sK1) = u1_struct_0(sK2)
    & l1_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f32,f31,f30,f29])).

fof(f55,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v3_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v3_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
                    & v3_pre_topc(sK0(X0,X1,X2),X1)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v3_pre_topc(sK0(X0,X1,X2),X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2452,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2855,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2452])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_353,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_3])).

cnf(c_2447,plain,
    ( ~ l1_pre_topc(X0_53)
    | u1_struct_0(X0_53) = k2_struct_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_353])).

cnf(c_2860,plain,
    ( u1_struct_0(X0_53) = k2_struct_0(X0_53)
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2447])).

cnf(c_3692,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2855,c_2860])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2450,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2857,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2450])).

cnf(c_3694,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2857,c_2860])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2451,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2856,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2451])).

cnf(c_3693,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2856,c_2860])).

cnf(c_22,negated_conjecture,
    ( u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2453,negated_conjecture,
    ( u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3983,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK2) ),
    inference(demodulation,[status(thm)],[c_3693,c_2453])).

cnf(c_4269,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_3694,c_3983])).

cnf(c_4404,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_4269,c_3693])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_398,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X2) = k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_399,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v5_pre_topc(sK4,X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k2_struct_0(X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_2443,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ v5_pre_topc(sK4,X0_53,X1_53)
    | ~ v3_pre_topc(X0_51,X1_53)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK4,X0_51),X0_53)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | k2_struct_0(X1_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_399])).

cnf(c_2861,plain,
    ( k2_struct_0(X0_53) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X1_53),u1_struct_0(X0_53)) != iProver_top
    | v5_pre_topc(sK4,X1_53,X0_53) != iProver_top
    | v3_pre_topc(X0_51,X0_53) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1_53),u1_struct_0(X0_53),sK4,X0_51),X1_53) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X0_53)))) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2443])).

cnf(c_5826,plain,
    ( k2_struct_0(X0_53) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | v5_pre_topc(sK4,sK2,X0_53) != iProver_top
    | v3_pre_topc(X0_51,X0_53) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_53),sK4,X0_51),sK2) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4404,c_2861])).

cnf(c_5845,plain,
    ( k2_struct_0(X0_53) = k1_xboole_0
    | v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(X0_53)) != iProver_top
    | v5_pre_topc(sK4,sK2,X0_53) != iProver_top
    | v3_pre_topc(X0_51,X0_53) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_53),sK4,X0_51),sK2) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5826,c_4404])).

cnf(c_32,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9500,plain,
    ( l1_pre_topc(X0_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_53),sK4,X0_51),sK2) = iProver_top
    | v3_pre_topc(X0_51,X0_53) != iProver_top
    | v5_pre_topc(sK4,sK2,X0_53) != iProver_top
    | v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(X0_53)) != iProver_top
    | k2_struct_0(X0_53) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5845,c_32])).

cnf(c_9501,plain,
    ( k2_struct_0(X0_53) = k1_xboole_0
    | v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(X0_53)) != iProver_top
    | v5_pre_topc(sK4,sK2,X0_53) != iProver_top
    | v3_pre_topc(X0_51,X0_53) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_53),sK4,X0_51),sK2) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_9500])).

cnf(c_9515,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v3_pre_topc(X0_51,sK3) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK2) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3692,c_9501])).

cnf(c_9552,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v3_pre_topc(X0_51,sK3) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK2) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9515,c_3692])).

cnf(c_18,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_38,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2454,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2854,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2454])).

cnf(c_2884,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2854,c_2453])).

cnf(c_3844,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3692,c_2884])).

cnf(c_4480,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3844,c_3694])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2456,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2852,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2456])).

cnf(c_2887,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2852,c_2453])).

cnf(c_3843,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3692,c_2887])).

cnf(c_4484,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3843,c_3694])).

cnf(c_4576,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_53,sK3) != iProver_top
    | v3_pre_topc(X0_51,sK3) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,X0_51),X0_53) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3692,c_2861])).

cnf(c_4586,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X0_53),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_53,sK3) != iProver_top
    | v3_pre_topc(X0_51,sK3) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,X0_51),X0_53) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4576,c_3692])).

cnf(c_34,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2462,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_2483,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2462])).

cnf(c_2505,plain,
    ( ~ l1_pre_topc(sK3)
    | u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2447])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_321,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_339,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_321])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_371,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_339,c_24])).

cnf(c_372,plain,
    ( ~ l1_pre_topc(sK3)
    | u1_struct_0(sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_374,plain,
    ( u1_struct_0(sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_23])).

cnf(c_2446,plain,
    ( u1_struct_0(sK3) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_374])).

cnf(c_2464,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_3100,plain,
    ( u1_struct_0(sK3) != X0_52
    | u1_struct_0(sK3) = k1_xboole_0
    | k1_xboole_0 != X0_52 ),
    inference(instantiation,[status(thm)],[c_2464])).

cnf(c_3171,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | u1_struct_0(sK3) = k1_xboole_0
    | k1_xboole_0 != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3100])).

cnf(c_3356,plain,
    ( k2_struct_0(sK3) != X0_52
    | k1_xboole_0 != X0_52
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2464])).

cnf(c_3357,plain,
    ( k2_struct_0(sK3) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3356])).

cnf(c_7918,plain,
    ( l1_pre_topc(X0_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),k2_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,X0_51),X0_53) = iProver_top
    | v3_pre_topc(X0_51,sK3) != iProver_top
    | v5_pre_topc(sK4,X0_53,sK3) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(X0_53),k2_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4586,c_23,c_34,c_2483,c_2505,c_2446,c_3171,c_3357])).

cnf(c_7919,plain,
    ( v1_funct_2(sK4,u1_struct_0(X0_53),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_53,sK3) != iProver_top
    | v3_pre_topc(X0_51,sK3) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,X0_51),X0_53) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_7918])).

cnf(c_7933,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v3_pre_topc(X0_51,sK3) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK2) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4404,c_7919])).

cnf(c_7941,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v3_pre_topc(X0_51,sK3) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK2) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7933,c_4404])).

cnf(c_9652,plain,
    ( v3_pre_topc(X0_51,sK3) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK2) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9552,c_32,c_38,c_4480,c_4484,c_7941])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2459,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | m1_subset_1(k8_relset_1(X0_52,X1_52,X0_51,X1_51),k1_zfmisc_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2849,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(k8_relset_1(X0_52,X1_52,X0_51,X1_51),k1_zfmisc_1(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2459])).

cnf(c_5,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2457,plain,
    ( ~ v3_pre_topc(X0_51,X0_53)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53)))
    | r2_hidden(X0_51,u1_pre_topc(X0_53))
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2851,plain,
    ( v3_pre_topc(X0_51,X0_53) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | r2_hidden(X0_51,u1_pre_topc(X0_53)) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2457])).

cnf(c_3302,plain,
    ( v3_pre_topc(X0_51,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0_51,u1_pre_topc(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2453,c_2851])).

cnf(c_3374,plain,
    ( r2_hidden(X0_51,u1_pre_topc(sK2)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_pre_topc(X0_51,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3302,c_32])).

cnf(c_3375,plain,
    ( v3_pre_topc(X0_51,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0_51,u1_pre_topc(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3374])).

cnf(c_3383,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK1),X0_52,X0_51,X1_51),sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_52))) != iProver_top
    | r2_hidden(k8_relset_1(u1_struct_0(sK1),X0_52,X0_51,X1_51),u1_pre_topc(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2849,c_3375])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_306,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | u1_pre_topc(sK2) != X1
    | u1_pre_topc(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_307,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK2))
    | r2_hidden(X0,u1_pre_topc(sK1)) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_2448,plain,
    ( ~ r2_hidden(X0_51,u1_pre_topc(sK2))
    | r2_hidden(X0_51,u1_pre_topc(sK1)) ),
    inference(subtyping,[status(esa)],[c_307])).

cnf(c_2859,plain,
    ( r2_hidden(X0_51,u1_pre_topc(sK2)) != iProver_top
    | r2_hidden(X0_51,u1_pre_topc(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2448])).

cnf(c_3484,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK1),X0_52,X0_51,X1_51),sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_52))) != iProver_top
    | r2_hidden(k8_relset_1(u1_struct_0(sK1),X0_52,X0_51,X1_51),u1_pre_topc(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3383,c_2859])).

cnf(c_6002,plain,
    ( v3_pre_topc(k8_relset_1(k2_struct_0(sK1),X0_52,X0_51,X1_51),sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X0_52))) != iProver_top
    | r2_hidden(k8_relset_1(k2_struct_0(sK1),X0_52,X0_51,X1_51),u1_pre_topc(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3484,c_3694])).

cnf(c_4,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2458,plain,
    ( v3_pre_topc(X0_51,X0_53)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ r2_hidden(X0_51,u1_pre_topc(X0_53))
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2850,plain,
    ( v3_pre_topc(X0_51,X0_53) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | r2_hidden(X0_51,u1_pre_topc(X0_53)) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2458])).

cnf(c_4156,plain,
    ( v3_pre_topc(X0_51,sK1) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r2_hidden(X0_51,u1_pre_topc(sK1)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3983,c_2850])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5021,plain,
    ( r2_hidden(X0_51,u1_pre_topc(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | v3_pre_topc(X0_51,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4156,c_30])).

cnf(c_5022,plain,
    ( v3_pre_topc(X0_51,sK1) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r2_hidden(X0_51,u1_pre_topc(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5021])).

cnf(c_5027,plain,
    ( v3_pre_topc(X0_51,sK1) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | r2_hidden(X0_51,u1_pre_topc(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5022,c_4269])).

cnf(c_5034,plain,
    ( v3_pre_topc(k8_relset_1(k2_struct_0(sK1),X0_52,X0_51,X1_51),sK1) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X0_52))) != iProver_top
    | r2_hidden(k8_relset_1(k2_struct_0(sK1),X0_52,X0_51,X1_51),u1_pre_topc(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2849,c_5027])).

cnf(c_6857,plain,
    ( v3_pre_topc(k8_relset_1(k2_struct_0(sK1),X0_52,X0_51,X1_51),sK2) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),X0_52,X0_51,X1_51),sK1) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X0_52))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6002,c_5034])).

cnf(c_9661,plain,
    ( v3_pre_topc(X0_51,sK3) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK1) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9652,c_6857])).

cnf(c_9813,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK1) = iProver_top
    | v3_pre_topc(X0_51,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9661,c_4484])).

cnf(c_9814,plain,
    ( v3_pre_topc(X0_51,sK3) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK1) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9813])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_572,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X2) = k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_573,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | v5_pre_topc(sK4,X0,X1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK0(X0,X1,sK4)),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k2_struct_0(X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_2437,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | v5_pre_topc(sK4,X0_53,X1_53)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK4,sK0(X0_53,X1_53,sK4)),X0_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | k2_struct_0(X1_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_573])).

cnf(c_2867,plain,
    ( k2_struct_0(X0_53) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X1_53),u1_struct_0(X0_53)) != iProver_top
    | v5_pre_topc(sK4,X1_53,X0_53) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1_53),u1_struct_0(X0_53),sK4,sK0(X1_53,X0_53,sK4)),X1_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X0_53)))) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2437])).

cnf(c_5638,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_53,sK3) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,sK0(X0_53,sK3,sK4)),X0_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3692,c_2867])).

cnf(c_5646,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X0_53),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_53,sK3) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,sK0(X0_53,sK3,sK4)),X0_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5638,c_3692])).

cnf(c_7971,plain,
    ( l1_pre_topc(X0_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),k2_struct_0(sK3)))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,sK0(X0_53,sK3,sK4)),X0_53) != iProver_top
    | v5_pre_topc(sK4,X0_53,sK3) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(X0_53),k2_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5646,c_23,c_34,c_2483,c_2505,c_2446,c_3171,c_3357])).

cnf(c_7972,plain,
    ( v1_funct_2(sK4,u1_struct_0(X0_53),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_53,sK3) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,sK0(X0_53,sK3,sK4)),X0_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_7971])).

cnf(c_7983,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK3) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,sK0(sK1,sK3,sK4)),sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3694,c_7972])).

cnf(c_8002,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK3) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,sK0(sK1,sK3,sK4)),sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7983,c_3694])).

cnf(c_16,negated_conjecture,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_153,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_20])).

cnf(c_154,negated_conjecture,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) ),
    inference(renaming,[status(thm)],[c_153])).

cnf(c_2449,negated_conjecture,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_154])).

cnf(c_2858,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2449])).

cnf(c_2921,plain,
    ( v5_pre_topc(sK4,sK1,sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2858,c_2887,c_2884])).

cnf(c_8170,plain,
    ( v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,sK0(sK1,sK3,sK4)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8002,c_30,c_2921,c_4480,c_4484])).

cnf(c_9822,plain,
    ( v3_pre_topc(sK0(sK1,sK3,sK4),sK3) != iProver_top
    | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9814,c_8170])).

cnf(c_2467,plain,
    ( ~ m1_subset_1(X0_51,X0_54)
    | m1_subset_1(X1_51,X1_54)
    | X1_54 != X0_54
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_3262,plain,
    ( m1_subset_1(X0_51,X0_54)
    | ~ m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(u1_struct_0(X0_53)))
    | X0_54 != k1_zfmisc_1(u1_struct_0(X0_53))
    | X0_51 != sK0(sK1,X0_53,sK4) ),
    inference(instantiation,[status(thm)],[c_2467])).

cnf(c_3564,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(X0_52))
    | ~ m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(u1_struct_0(X0_53)))
    | k1_zfmisc_1(X0_52) != k1_zfmisc_1(u1_struct_0(X0_53))
    | X0_51 != sK0(sK1,X0_53,sK4) ),
    inference(instantiation,[status(thm)],[c_3262])).

cnf(c_5061,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(X0_53)))
    | ~ m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(u1_struct_0(X0_53)))
    | k1_zfmisc_1(k2_struct_0(X0_53)) != k1_zfmisc_1(u1_struct_0(X0_53))
    | X0_51 != sK0(sK1,X0_53,sK4) ),
    inference(instantiation,[status(thm)],[c_3564])).

cnf(c_6654,plain,
    ( ~ m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(u1_struct_0(X0_53)))
    | m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(k2_struct_0(X0_53)))
    | k1_zfmisc_1(k2_struct_0(X0_53)) != k1_zfmisc_1(u1_struct_0(X0_53))
    | sK0(sK1,X0_53,sK4) != sK0(sK1,X0_53,sK4) ),
    inference(instantiation,[status(thm)],[c_5061])).

cnf(c_6656,plain,
    ( k1_zfmisc_1(k2_struct_0(X0_53)) != k1_zfmisc_1(u1_struct_0(X0_53))
    | sK0(sK1,X0_53,sK4) != sK0(sK1,X0_53,sK4)
    | m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(k2_struct_0(X0_53))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6654])).

cnf(c_6658,plain,
    ( k1_zfmisc_1(k2_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | sK0(sK1,sK3,sK4) != sK0(sK1,sK3,sK4)
    | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6656])).

cnf(c_2466,plain,
    ( k1_zfmisc_1(X0_52) = k1_zfmisc_1(X1_52)
    | X0_52 != X1_52 ),
    theory(equality)).

cnf(c_3565,plain,
    ( k1_zfmisc_1(X0_52) = k1_zfmisc_1(u1_struct_0(X0_53))
    | X0_52 != u1_struct_0(X0_53) ),
    inference(instantiation,[status(thm)],[c_2466])).

cnf(c_4438,plain,
    ( k1_zfmisc_1(k2_struct_0(X0_53)) = k1_zfmisc_1(u1_struct_0(X0_53))
    | k2_struct_0(X0_53) != u1_struct_0(X0_53) ),
    inference(instantiation,[status(thm)],[c_3565])).

cnf(c_4442,plain,
    ( k1_zfmisc_1(k2_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3))
    | k2_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4438])).

cnf(c_3182,plain,
    ( X0_52 != X1_52
    | k2_struct_0(X0_53) != X1_52
    | k2_struct_0(X0_53) = X0_52 ),
    inference(instantiation,[status(thm)],[c_2464])).

cnf(c_3419,plain,
    ( X0_52 != k2_struct_0(X0_53)
    | k2_struct_0(X0_53) = X0_52
    | k2_struct_0(X0_53) != k2_struct_0(X0_53) ),
    inference(instantiation,[status(thm)],[c_3182])).

cnf(c_3701,plain,
    ( u1_struct_0(X0_53) != k2_struct_0(X0_53)
    | k2_struct_0(X0_53) = u1_struct_0(X0_53)
    | k2_struct_0(X0_53) != k2_struct_0(X0_53) ),
    inference(instantiation,[status(thm)],[c_3419])).

cnf(c_3702,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | k2_struct_0(sK3) = u1_struct_0(sK3)
    | k2_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3701])).

cnf(c_2471,plain,
    ( X0_51 != X1_51
    | sK0(X0_53,X1_53,X0_51) = sK0(X0_53,X1_53,X1_51) ),
    theory(equality)).

cnf(c_3542,plain,
    ( X0_51 != sK4
    | sK0(sK1,X0_53,X0_51) = sK0(sK1,X0_53,sK4) ),
    inference(instantiation,[status(thm)],[c_2471])).

cnf(c_3545,plain,
    ( sK0(sK1,sK3,sK4) = sK0(sK1,sK3,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3542])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_464,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X2) = k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_465,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | v5_pre_topc(sK4,X0,X1)
    | m1_subset_1(sK0(X0,X1,sK4),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k2_struct_0(X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_2441,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | v5_pre_topc(sK4,X0_53,X1_53)
    | m1_subset_1(sK0(X0_53,X1_53,sK4),k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | k2_struct_0(X1_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_465])).

cnf(c_3186,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0_53))
    | v5_pre_topc(sK4,sK1,X0_53)
    | m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53))))
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK1)
    | k2_struct_0(X0_53) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2441])).

cnf(c_3194,plain,
    ( k2_struct_0(X0_53) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0_53)) != iProver_top
    | v5_pre_topc(sK4,sK1,X0_53) = iProver_top
    | m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(u1_struct_0(X0_53))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3186])).

cnf(c_3196,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK3) = iProver_top
    | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3194])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v3_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_518,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v3_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X2) = k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_519,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | v5_pre_topc(sK4,X0,X1)
    | v3_pre_topc(sK0(X0,X1,sK4),X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k2_struct_0(X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_2439,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | v5_pre_topc(sK4,X0_53,X1_53)
    | v3_pre_topc(sK0(X0_53,X1_53,sK4),X1_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | k2_struct_0(X1_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_519])).

cnf(c_3187,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0_53))
    | v5_pre_topc(sK4,sK1,X0_53)
    | v3_pre_topc(sK0(sK1,X0_53,sK4),X0_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53))))
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK1)
    | k2_struct_0(X0_53) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2439])).

cnf(c_3190,plain,
    ( k2_struct_0(X0_53) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0_53)) != iProver_top
    | v5_pre_topc(sK4,sK1,X0_53) = iProver_top
    | v3_pre_topc(sK0(sK1,X0_53,sK4),X0_53) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3187])).

cnf(c_3192,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK3) = iProver_top
    | v3_pre_topc(sK0(sK1,sK3,sK4),sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3190])).

cnf(c_3179,plain,
    ( k2_struct_0(X0_53) = k2_struct_0(X0_53) ),
    inference(instantiation,[status(thm)],[c_2462])).

cnf(c_3181,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3179])).

cnf(c_2461,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_2482,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2461])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9822,c_6658,c_4442,c_3702,c_3545,c_3357,c_3196,c_3192,c_3181,c_3171,c_2884,c_2921,c_2887,c_2446,c_2505,c_2483,c_2482,c_34,c_23,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:22:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.33/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/0.98  
% 3.33/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/0.98  
% 3.33/0.98  ------  iProver source info
% 3.33/0.98  
% 3.33/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.33/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/0.98  git: non_committed_changes: false
% 3.33/0.98  git: last_make_outside_of_git: false
% 3.33/0.98  
% 3.33/0.98  ------ 
% 3.33/0.98  
% 3.33/0.98  ------ Input Options
% 3.33/0.98  
% 3.33/0.98  --out_options                           all
% 3.33/0.98  --tptp_safe_out                         true
% 3.33/0.98  --problem_path                          ""
% 3.33/0.98  --include_path                          ""
% 3.33/0.98  --clausifier                            res/vclausify_rel
% 3.33/0.98  --clausifier_options                    --mode clausify
% 3.33/0.98  --stdin                                 false
% 3.33/0.98  --stats_out                             all
% 3.33/0.98  
% 3.33/0.98  ------ General Options
% 3.33/0.98  
% 3.33/0.98  --fof                                   false
% 3.33/0.98  --time_out_real                         305.
% 3.33/0.98  --time_out_virtual                      -1.
% 3.33/0.98  --symbol_type_check                     false
% 3.33/0.98  --clausify_out                          false
% 3.33/0.98  --sig_cnt_out                           false
% 3.33/0.98  --trig_cnt_out                          false
% 3.33/0.98  --trig_cnt_out_tolerance                1.
% 3.33/0.98  --trig_cnt_out_sk_spl                   false
% 3.33/0.98  --abstr_cl_out                          false
% 3.33/0.98  
% 3.33/0.98  ------ Global Options
% 3.33/0.98  
% 3.33/0.98  --schedule                              default
% 3.33/0.98  --add_important_lit                     false
% 3.33/0.98  --prop_solver_per_cl                    1000
% 3.33/0.98  --min_unsat_core                        false
% 3.33/0.98  --soft_assumptions                      false
% 3.33/0.98  --soft_lemma_size                       3
% 3.33/0.98  --prop_impl_unit_size                   0
% 3.33/0.98  --prop_impl_unit                        []
% 3.33/0.98  --share_sel_clauses                     true
% 3.33/0.98  --reset_solvers                         false
% 3.33/0.98  --bc_imp_inh                            [conj_cone]
% 3.33/0.98  --conj_cone_tolerance                   3.
% 3.33/0.98  --extra_neg_conj                        none
% 3.33/0.98  --large_theory_mode                     true
% 3.33/0.98  --prolific_symb_bound                   200
% 3.33/0.98  --lt_threshold                          2000
% 3.33/0.98  --clause_weak_htbl                      true
% 3.33/0.98  --gc_record_bc_elim                     false
% 3.33/0.98  
% 3.33/0.98  ------ Preprocessing Options
% 3.33/0.98  
% 3.33/0.98  --preprocessing_flag                    true
% 3.33/0.98  --time_out_prep_mult                    0.1
% 3.33/0.98  --splitting_mode                        input
% 3.33/0.98  --splitting_grd                         true
% 3.33/0.98  --splitting_cvd                         false
% 3.33/0.98  --splitting_cvd_svl                     false
% 3.33/0.98  --splitting_nvd                         32
% 3.33/0.98  --sub_typing                            true
% 3.33/0.98  --prep_gs_sim                           true
% 3.33/0.98  --prep_unflatten                        true
% 3.33/0.98  --prep_res_sim                          true
% 3.33/0.98  --prep_upred                            true
% 3.33/0.98  --prep_sem_filter                       exhaustive
% 3.33/0.98  --prep_sem_filter_out                   false
% 3.33/0.98  --pred_elim                             true
% 3.33/0.98  --res_sim_input                         true
% 3.33/0.98  --eq_ax_congr_red                       true
% 3.33/0.98  --pure_diseq_elim                       true
% 3.33/0.98  --brand_transform                       false
% 3.33/0.98  --non_eq_to_eq                          false
% 3.33/0.98  --prep_def_merge                        true
% 3.33/0.98  --prep_def_merge_prop_impl              false
% 3.33/0.98  --prep_def_merge_mbd                    true
% 3.33/0.98  --prep_def_merge_tr_red                 false
% 3.33/0.98  --prep_def_merge_tr_cl                  false
% 3.33/0.98  --smt_preprocessing                     true
% 3.33/0.98  --smt_ac_axioms                         fast
% 3.33/0.98  --preprocessed_out                      false
% 3.33/0.98  --preprocessed_stats                    false
% 3.33/0.98  
% 3.33/0.98  ------ Abstraction refinement Options
% 3.33/0.98  
% 3.33/0.98  --abstr_ref                             []
% 3.33/0.98  --abstr_ref_prep                        false
% 3.33/0.98  --abstr_ref_until_sat                   false
% 3.33/0.98  --abstr_ref_sig_restrict                funpre
% 3.33/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/0.98  --abstr_ref_under                       []
% 3.33/0.98  
% 3.33/0.98  ------ SAT Options
% 3.33/0.98  
% 3.33/0.98  --sat_mode                              false
% 3.33/0.98  --sat_fm_restart_options                ""
% 3.33/0.98  --sat_gr_def                            false
% 3.33/0.98  --sat_epr_types                         true
% 3.33/0.98  --sat_non_cyclic_types                  false
% 3.33/0.98  --sat_finite_models                     false
% 3.33/0.98  --sat_fm_lemmas                         false
% 3.33/0.98  --sat_fm_prep                           false
% 3.33/0.98  --sat_fm_uc_incr                        true
% 3.33/0.98  --sat_out_model                         small
% 3.33/0.98  --sat_out_clauses                       false
% 3.33/0.98  
% 3.33/0.98  ------ QBF Options
% 3.33/0.98  
% 3.33/0.98  --qbf_mode                              false
% 3.33/0.98  --qbf_elim_univ                         false
% 3.33/0.98  --qbf_dom_inst                          none
% 3.33/0.98  --qbf_dom_pre_inst                      false
% 3.33/0.98  --qbf_sk_in                             false
% 3.33/0.98  --qbf_pred_elim                         true
% 3.33/0.98  --qbf_split                             512
% 3.33/0.98  
% 3.33/0.98  ------ BMC1 Options
% 3.33/0.98  
% 3.33/0.98  --bmc1_incremental                      false
% 3.33/0.98  --bmc1_axioms                           reachable_all
% 3.33/0.98  --bmc1_min_bound                        0
% 3.33/0.98  --bmc1_max_bound                        -1
% 3.33/0.98  --bmc1_max_bound_default                -1
% 3.33/0.98  --bmc1_symbol_reachability              true
% 3.33/0.98  --bmc1_property_lemmas                  false
% 3.33/0.98  --bmc1_k_induction                      false
% 3.33/0.98  --bmc1_non_equiv_states                 false
% 3.33/0.98  --bmc1_deadlock                         false
% 3.33/0.98  --bmc1_ucm                              false
% 3.33/0.98  --bmc1_add_unsat_core                   none
% 3.33/0.98  --bmc1_unsat_core_children              false
% 3.33/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/0.98  --bmc1_out_stat                         full
% 3.33/0.98  --bmc1_ground_init                      false
% 3.33/0.98  --bmc1_pre_inst_next_state              false
% 3.33/0.98  --bmc1_pre_inst_state                   false
% 3.33/0.98  --bmc1_pre_inst_reach_state             false
% 3.33/0.98  --bmc1_out_unsat_core                   false
% 3.33/0.98  --bmc1_aig_witness_out                  false
% 3.33/0.98  --bmc1_verbose                          false
% 3.33/0.98  --bmc1_dump_clauses_tptp                false
% 3.33/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.33/0.98  --bmc1_dump_file                        -
% 3.33/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.33/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.33/0.98  --bmc1_ucm_extend_mode                  1
% 3.33/0.98  --bmc1_ucm_init_mode                    2
% 3.33/0.98  --bmc1_ucm_cone_mode                    none
% 3.33/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.33/0.98  --bmc1_ucm_relax_model                  4
% 3.33/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.33/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/0.98  --bmc1_ucm_layered_model                none
% 3.33/0.98  --bmc1_ucm_max_lemma_size               10
% 3.33/0.98  
% 3.33/0.98  ------ AIG Options
% 3.33/0.98  
% 3.33/0.98  --aig_mode                              false
% 3.33/0.98  
% 3.33/0.98  ------ Instantiation Options
% 3.33/0.98  
% 3.33/0.98  --instantiation_flag                    true
% 3.33/0.98  --inst_sos_flag                         false
% 3.33/0.98  --inst_sos_phase                        true
% 3.33/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/0.98  --inst_lit_sel_side                     num_symb
% 3.33/0.98  --inst_solver_per_active                1400
% 3.33/0.98  --inst_solver_calls_frac                1.
% 3.33/0.98  --inst_passive_queue_type               priority_queues
% 3.33/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/0.98  --inst_passive_queues_freq              [25;2]
% 3.33/0.98  --inst_dismatching                      true
% 3.33/0.98  --inst_eager_unprocessed_to_passive     true
% 3.33/0.98  --inst_prop_sim_given                   true
% 3.33/0.98  --inst_prop_sim_new                     false
% 3.33/0.98  --inst_subs_new                         false
% 3.33/0.98  --inst_eq_res_simp                      false
% 3.33/0.98  --inst_subs_given                       false
% 3.33/0.98  --inst_orphan_elimination               true
% 3.33/0.98  --inst_learning_loop_flag               true
% 3.33/0.98  --inst_learning_start                   3000
% 3.33/0.98  --inst_learning_factor                  2
% 3.33/0.98  --inst_start_prop_sim_after_learn       3
% 3.33/0.98  --inst_sel_renew                        solver
% 3.33/0.98  --inst_lit_activity_flag                true
% 3.33/0.98  --inst_restr_to_given                   false
% 3.33/0.98  --inst_activity_threshold               500
% 3.33/0.98  --inst_out_proof                        true
% 3.33/0.98  
% 3.33/0.98  ------ Resolution Options
% 3.33/0.98  
% 3.33/0.98  --resolution_flag                       true
% 3.33/0.98  --res_lit_sel                           adaptive
% 3.33/0.98  --res_lit_sel_side                      none
% 3.33/0.98  --res_ordering                          kbo
% 3.33/0.98  --res_to_prop_solver                    active
% 3.33/0.98  --res_prop_simpl_new                    false
% 3.33/0.98  --res_prop_simpl_given                  true
% 3.33/0.98  --res_passive_queue_type                priority_queues
% 3.33/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/0.98  --res_passive_queues_freq               [15;5]
% 3.33/0.98  --res_forward_subs                      full
% 3.33/0.98  --res_backward_subs                     full
% 3.33/0.98  --res_forward_subs_resolution           true
% 3.33/0.98  --res_backward_subs_resolution          true
% 3.33/0.98  --res_orphan_elimination                true
% 3.33/0.98  --res_time_limit                        2.
% 3.33/0.98  --res_out_proof                         true
% 3.33/0.98  
% 3.33/0.98  ------ Superposition Options
% 3.33/0.98  
% 3.33/0.98  --superposition_flag                    true
% 3.33/0.98  --sup_passive_queue_type                priority_queues
% 3.33/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.33/0.98  --demod_completeness_check              fast
% 3.33/0.98  --demod_use_ground                      true
% 3.33/0.98  --sup_to_prop_solver                    passive
% 3.33/0.98  --sup_prop_simpl_new                    true
% 3.33/0.98  --sup_prop_simpl_given                  true
% 3.33/0.98  --sup_fun_splitting                     false
% 3.33/0.98  --sup_smt_interval                      50000
% 3.33/0.98  
% 3.33/0.98  ------ Superposition Simplification Setup
% 3.33/0.98  
% 3.33/0.98  --sup_indices_passive                   []
% 3.33/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.98  --sup_full_bw                           [BwDemod]
% 3.33/0.98  --sup_immed_triv                        [TrivRules]
% 3.33/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.98  --sup_immed_bw_main                     []
% 3.33/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.98  
% 3.33/0.98  ------ Combination Options
% 3.33/0.98  
% 3.33/0.98  --comb_res_mult                         3
% 3.33/0.98  --comb_sup_mult                         2
% 3.33/0.98  --comb_inst_mult                        10
% 3.33/0.98  
% 3.33/0.98  ------ Debug Options
% 3.33/0.98  
% 3.33/0.98  --dbg_backtrace                         false
% 3.33/0.98  --dbg_dump_prop_clauses                 false
% 3.33/0.98  --dbg_dump_prop_clauses_file            -
% 3.33/0.98  --dbg_out_stat                          false
% 3.33/0.98  ------ Parsing...
% 3.33/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/0.98  
% 3.33/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.33/0.98  
% 3.33/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/0.98  
% 3.33/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.33/0.98  ------ Proving...
% 3.33/0.98  ------ Problem Properties 
% 3.33/0.98  
% 3.33/0.98  
% 3.33/0.98  clauses                                 24
% 3.33/0.98  conjectures                             8
% 3.33/0.98  EPR                                     4
% 3.33/0.98  Horn                                    18
% 3.33/0.98  unary                                   10
% 3.33/0.98  binary                                  3
% 3.33/0.98  lits                                    87
% 3.33/0.98  lits eq                                 13
% 3.33/0.98  fd_pure                                 0
% 3.33/0.98  fd_pseudo                               0
% 3.33/0.98  fd_cond                                 0
% 3.33/0.98  fd_pseudo_cond                          0
% 3.33/0.98  AC symbols                              0
% 3.33/0.98  
% 3.33/0.98  ------ Schedule dynamic 5 is on 
% 3.33/0.98  
% 3.33/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.33/0.98  
% 3.33/0.98  
% 3.33/0.98  ------ 
% 3.33/0.98  Current options:
% 3.33/0.98  ------ 
% 3.33/0.98  
% 3.33/0.98  ------ Input Options
% 3.33/0.98  
% 3.33/0.98  --out_options                           all
% 3.33/0.98  --tptp_safe_out                         true
% 3.33/0.98  --problem_path                          ""
% 3.33/0.98  --include_path                          ""
% 3.33/0.98  --clausifier                            res/vclausify_rel
% 3.33/0.98  --clausifier_options                    --mode clausify
% 3.33/0.98  --stdin                                 false
% 3.33/0.98  --stats_out                             all
% 3.33/0.98  
% 3.33/0.98  ------ General Options
% 3.33/0.98  
% 3.33/0.98  --fof                                   false
% 3.33/0.98  --time_out_real                         305.
% 3.33/0.98  --time_out_virtual                      -1.
% 3.33/0.98  --symbol_type_check                     false
% 3.33/0.98  --clausify_out                          false
% 3.33/0.98  --sig_cnt_out                           false
% 3.33/0.98  --trig_cnt_out                          false
% 3.33/0.98  --trig_cnt_out_tolerance                1.
% 3.33/0.98  --trig_cnt_out_sk_spl                   false
% 3.33/0.98  --abstr_cl_out                          false
% 3.33/0.98  
% 3.33/0.98  ------ Global Options
% 3.33/0.98  
% 3.33/0.98  --schedule                              default
% 3.33/0.98  --add_important_lit                     false
% 3.33/0.98  --prop_solver_per_cl                    1000
% 3.33/0.98  --min_unsat_core                        false
% 3.33/0.98  --soft_assumptions                      false
% 3.33/0.98  --soft_lemma_size                       3
% 3.33/0.98  --prop_impl_unit_size                   0
% 3.33/0.98  --prop_impl_unit                        []
% 3.33/0.98  --share_sel_clauses                     true
% 3.33/0.98  --reset_solvers                         false
% 3.33/0.98  --bc_imp_inh                            [conj_cone]
% 3.33/0.98  --conj_cone_tolerance                   3.
% 3.33/0.98  --extra_neg_conj                        none
% 3.33/0.98  --large_theory_mode                     true
% 3.33/0.98  --prolific_symb_bound                   200
% 3.33/0.98  --lt_threshold                          2000
% 3.33/0.98  --clause_weak_htbl                      true
% 3.33/0.98  --gc_record_bc_elim                     false
% 3.33/0.98  
% 3.33/0.98  ------ Preprocessing Options
% 3.33/0.98  
% 3.33/0.98  --preprocessing_flag                    true
% 3.33/0.98  --time_out_prep_mult                    0.1
% 3.33/0.98  --splitting_mode                        input
% 3.33/0.98  --splitting_grd                         true
% 3.33/0.98  --splitting_cvd                         false
% 3.33/0.98  --splitting_cvd_svl                     false
% 3.33/0.98  --splitting_nvd                         32
% 3.33/0.98  --sub_typing                            true
% 3.33/0.98  --prep_gs_sim                           true
% 3.33/0.98  --prep_unflatten                        true
% 3.33/0.98  --prep_res_sim                          true
% 3.33/0.98  --prep_upred                            true
% 3.33/0.98  --prep_sem_filter                       exhaustive
% 3.33/0.98  --prep_sem_filter_out                   false
% 3.33/0.98  --pred_elim                             true
% 3.33/0.98  --res_sim_input                         true
% 3.33/0.98  --eq_ax_congr_red                       true
% 3.33/0.98  --pure_diseq_elim                       true
% 3.33/0.98  --brand_transform                       false
% 3.33/0.98  --non_eq_to_eq                          false
% 3.33/0.98  --prep_def_merge                        true
% 3.33/0.98  --prep_def_merge_prop_impl              false
% 3.33/0.98  --prep_def_merge_mbd                    true
% 3.33/0.98  --prep_def_merge_tr_red                 false
% 3.33/0.98  --prep_def_merge_tr_cl                  false
% 3.33/0.98  --smt_preprocessing                     true
% 3.33/0.98  --smt_ac_axioms                         fast
% 3.33/0.98  --preprocessed_out                      false
% 3.33/0.98  --preprocessed_stats                    false
% 3.33/0.98  
% 3.33/0.98  ------ Abstraction refinement Options
% 3.33/0.98  
% 3.33/0.98  --abstr_ref                             []
% 3.33/0.98  --abstr_ref_prep                        false
% 3.33/0.98  --abstr_ref_until_sat                   false
% 3.33/0.98  --abstr_ref_sig_restrict                funpre
% 3.33/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/0.98  --abstr_ref_under                       []
% 3.33/0.98  
% 3.33/0.98  ------ SAT Options
% 3.33/0.98  
% 3.33/0.98  --sat_mode                              false
% 3.33/0.98  --sat_fm_restart_options                ""
% 3.33/0.98  --sat_gr_def                            false
% 3.33/0.98  --sat_epr_types                         true
% 3.33/0.98  --sat_non_cyclic_types                  false
% 3.33/0.98  --sat_finite_models                     false
% 3.33/0.98  --sat_fm_lemmas                         false
% 3.33/0.98  --sat_fm_prep                           false
% 3.33/0.98  --sat_fm_uc_incr                        true
% 3.33/0.98  --sat_out_model                         small
% 3.33/0.98  --sat_out_clauses                       false
% 3.33/0.98  
% 3.33/0.98  ------ QBF Options
% 3.33/0.98  
% 3.33/0.98  --qbf_mode                              false
% 3.33/0.98  --qbf_elim_univ                         false
% 3.33/0.98  --qbf_dom_inst                          none
% 3.33/0.98  --qbf_dom_pre_inst                      false
% 3.33/0.98  --qbf_sk_in                             false
% 3.33/0.98  --qbf_pred_elim                         true
% 3.33/0.98  --qbf_split                             512
% 3.33/0.98  
% 3.33/0.98  ------ BMC1 Options
% 3.33/0.98  
% 3.33/0.98  --bmc1_incremental                      false
% 3.33/0.98  --bmc1_axioms                           reachable_all
% 3.33/0.98  --bmc1_min_bound                        0
% 3.33/0.98  --bmc1_max_bound                        -1
% 3.33/0.98  --bmc1_max_bound_default                -1
% 3.33/0.98  --bmc1_symbol_reachability              true
% 3.33/0.98  --bmc1_property_lemmas                  false
% 3.33/0.98  --bmc1_k_induction                      false
% 3.33/0.98  --bmc1_non_equiv_states                 false
% 3.33/0.98  --bmc1_deadlock                         false
% 3.33/0.98  --bmc1_ucm                              false
% 3.33/0.98  --bmc1_add_unsat_core                   none
% 3.33/0.98  --bmc1_unsat_core_children              false
% 3.33/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/0.98  --bmc1_out_stat                         full
% 3.33/0.98  --bmc1_ground_init                      false
% 3.33/0.98  --bmc1_pre_inst_next_state              false
% 3.33/0.98  --bmc1_pre_inst_state                   false
% 3.33/0.98  --bmc1_pre_inst_reach_state             false
% 3.33/0.98  --bmc1_out_unsat_core                   false
% 3.33/0.98  --bmc1_aig_witness_out                  false
% 3.33/0.98  --bmc1_verbose                          false
% 3.33/0.98  --bmc1_dump_clauses_tptp                false
% 3.33/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.33/0.98  --bmc1_dump_file                        -
% 3.33/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.33/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.33/0.98  --bmc1_ucm_extend_mode                  1
% 3.33/0.98  --bmc1_ucm_init_mode                    2
% 3.33/0.98  --bmc1_ucm_cone_mode                    none
% 3.33/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.33/0.98  --bmc1_ucm_relax_model                  4
% 3.33/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.33/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/0.98  --bmc1_ucm_layered_model                none
% 3.33/0.98  --bmc1_ucm_max_lemma_size               10
% 3.33/0.98  
% 3.33/0.98  ------ AIG Options
% 3.33/0.98  
% 3.33/0.98  --aig_mode                              false
% 3.33/0.98  
% 3.33/0.98  ------ Instantiation Options
% 3.33/0.98  
% 3.33/0.98  --instantiation_flag                    true
% 3.33/0.98  --inst_sos_flag                         false
% 3.33/0.98  --inst_sos_phase                        true
% 3.33/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/0.98  --inst_lit_sel_side                     none
% 3.33/0.98  --inst_solver_per_active                1400
% 3.33/0.98  --inst_solver_calls_frac                1.
% 3.33/0.98  --inst_passive_queue_type               priority_queues
% 3.33/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/0.98  --inst_passive_queues_freq              [25;2]
% 3.33/0.98  --inst_dismatching                      true
% 3.33/0.98  --inst_eager_unprocessed_to_passive     true
% 3.33/0.98  --inst_prop_sim_given                   true
% 3.33/0.98  --inst_prop_sim_new                     false
% 3.33/0.98  --inst_subs_new                         false
% 3.33/0.98  --inst_eq_res_simp                      false
% 3.33/0.98  --inst_subs_given                       false
% 3.33/0.98  --inst_orphan_elimination               true
% 3.33/0.98  --inst_learning_loop_flag               true
% 3.33/0.98  --inst_learning_start                   3000
% 3.33/0.98  --inst_learning_factor                  2
% 3.33/0.98  --inst_start_prop_sim_after_learn       3
% 3.33/0.98  --inst_sel_renew                        solver
% 3.33/0.98  --inst_lit_activity_flag                true
% 3.33/0.98  --inst_restr_to_given                   false
% 3.33/0.98  --inst_activity_threshold               500
% 3.33/0.98  --inst_out_proof                        true
% 3.33/0.98  
% 3.33/0.98  ------ Resolution Options
% 3.33/0.98  
% 3.33/0.98  --resolution_flag                       false
% 3.33/0.98  --res_lit_sel                           adaptive
% 3.33/0.98  --res_lit_sel_side                      none
% 3.33/0.98  --res_ordering                          kbo
% 3.33/0.98  --res_to_prop_solver                    active
% 3.33/0.98  --res_prop_simpl_new                    false
% 3.33/0.98  --res_prop_simpl_given                  true
% 3.33/0.98  --res_passive_queue_type                priority_queues
% 3.33/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/0.98  --res_passive_queues_freq               [15;5]
% 3.33/0.98  --res_forward_subs                      full
% 3.33/0.98  --res_backward_subs                     full
% 3.33/0.98  --res_forward_subs_resolution           true
% 3.33/0.98  --res_backward_subs_resolution          true
% 3.33/0.98  --res_orphan_elimination                true
% 3.33/0.98  --res_time_limit                        2.
% 3.33/0.98  --res_out_proof                         true
% 3.33/0.98  
% 3.33/0.98  ------ Superposition Options
% 3.33/0.98  
% 3.33/0.98  --superposition_flag                    true
% 3.33/0.98  --sup_passive_queue_type                priority_queues
% 3.33/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.33/0.98  --demod_completeness_check              fast
% 3.33/0.98  --demod_use_ground                      true
% 3.33/0.98  --sup_to_prop_solver                    passive
% 3.33/0.98  --sup_prop_simpl_new                    true
% 3.33/0.98  --sup_prop_simpl_given                  true
% 3.33/0.98  --sup_fun_splitting                     false
% 3.33/0.98  --sup_smt_interval                      50000
% 3.33/0.98  
% 3.33/0.98  ------ Superposition Simplification Setup
% 3.33/0.98  
% 3.33/0.98  --sup_indices_passive                   []
% 3.33/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.98  --sup_full_bw                           [BwDemod]
% 3.33/0.98  --sup_immed_triv                        [TrivRules]
% 3.33/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.98  --sup_immed_bw_main                     []
% 3.33/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.98  
% 3.33/0.98  ------ Combination Options
% 3.33/0.98  
% 3.33/0.98  --comb_res_mult                         3
% 3.33/0.98  --comb_sup_mult                         2
% 3.33/0.98  --comb_inst_mult                        10
% 3.33/0.98  
% 3.33/0.98  ------ Debug Options
% 3.33/0.98  
% 3.33/0.98  --dbg_backtrace                         false
% 3.33/0.98  --dbg_dump_prop_clauses                 false
% 3.33/0.98  --dbg_dump_prop_clauses_file            -
% 3.33/0.98  --dbg_out_stat                          false
% 3.33/0.98  
% 3.33/0.98  
% 3.33/0.98  
% 3.33/0.98  
% 3.33/0.98  ------ Proving...
% 3.33/0.98  
% 3.33/0.98  
% 3.33/0.98  % SZS status Theorem for theBenchmark.p
% 3.33/0.98  
% 3.33/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.33/0.98  
% 3.33/0.98  fof(f9,conjecture,(
% 3.33/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 3.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.99  
% 3.33/0.99  fof(f10,negated_conjecture,(
% 3.33/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 3.33/0.99    inference(negated_conjecture,[],[f9])).
% 3.33/0.99  
% 3.33/0.99  fof(f12,plain,(
% 3.33/0.99    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 3.33/0.99    inference(pure_predicate_removal,[],[f10])).
% 3.33/0.99  
% 3.33/0.99  fof(f22,plain,(
% 3.33/0.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3))) & (r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1))) & (l1_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.33/0.99    inference(ennf_transformation,[],[f12])).
% 3.33/0.99  
% 3.33/0.99  fof(f23,plain,(
% 3.33/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.33/0.99    inference(flattening,[],[f22])).
% 3.33/0.99  
% 3.33/0.99  fof(f32,plain,(
% 3.33/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(sK4,X0,X2) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(sK4,X1,X2) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(sK4))) )),
% 3.33/0.99    introduced(choice_axiom,[])).
% 3.33/0.99  
% 3.33/0.99  fof(f31,plain,(
% 3.33/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1) & l1_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(X3,X0,sK3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) & v5_pre_topc(X3,X1,sK3) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK3)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1) & l1_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 3.33/0.99    introduced(choice_axiom,[])).
% 3.33/0.99  
% 3.33/0.99  fof(f30,plain,(
% 3.33/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2)))) & v5_pre_topc(X3,sK2,X2) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(X0)) & u1_struct_0(sK2) = u1_struct_0(X0) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 3.33/0.99    introduced(choice_axiom,[])).
% 3.33/0.99  
% 3.33/0.99  fof(f29,plain,(
% 3.33/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK1,X2) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X1),u1_pre_topc(sK1)) & u1_struct_0(sK1) = u1_struct_0(X1) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.33/0.99    introduced(choice_axiom,[])).
% 3.33/0.99  
% 3.33/0.99  fof(f33,plain,(
% 3.33/0.99    ((((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) & u1_struct_0(sK1) = u1_struct_0(sK2) & l1_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.33/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f32,f31,f30,f29])).
% 3.33/0.99  
% 3.33/0.99  fof(f55,plain,(
% 3.33/0.99    l1_pre_topc(sK3)),
% 3.33/0.99    inference(cnf_transformation,[],[f33])).
% 3.33/0.99  
% 3.33/0.99  fof(f6,axiom,(
% 3.33/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.99  
% 3.33/0.99  fof(f17,plain,(
% 3.33/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.33/0.99    inference(ennf_transformation,[],[f6])).
% 3.33/0.99  
% 3.33/0.99  fof(f40,plain,(
% 3.33/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.33/0.99    inference(cnf_transformation,[],[f17])).
% 3.33/0.99  
% 3.33/0.99  fof(f4,axiom,(
% 3.33/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.99  
% 3.33/0.99  fof(f15,plain,(
% 3.33/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.33/0.99    inference(ennf_transformation,[],[f4])).
% 3.33/0.99  
% 3.33/0.99  fof(f37,plain,(
% 3.33/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.33/0.99    inference(cnf_transformation,[],[f15])).
% 3.33/0.99  
% 3.33/0.99  fof(f51,plain,(
% 3.33/0.99    l1_pre_topc(sK1)),
% 3.33/0.99    inference(cnf_transformation,[],[f33])).
% 3.33/0.99  
% 3.33/0.99  fof(f53,plain,(
% 3.33/0.99    l1_pre_topc(sK2)),
% 3.33/0.99    inference(cnf_transformation,[],[f33])).
% 3.33/0.99  
% 3.33/0.99  fof(f56,plain,(
% 3.33/0.99    u1_struct_0(sK1) = u1_struct_0(sK2)),
% 3.33/0.99    inference(cnf_transformation,[],[f33])).
% 3.33/0.99  
% 3.33/0.99  fof(f8,axiom,(
% 3.33/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 3.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.99  
% 3.33/0.99  fof(f20,plain,(
% 3.33/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.33/0.99    inference(ennf_transformation,[],[f8])).
% 3.33/0.99  
% 3.33/0.99  fof(f21,plain,(
% 3.33/0.99    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.33/0.99    inference(flattening,[],[f20])).
% 3.33/0.99  
% 3.33/0.99  fof(f25,plain,(
% 3.33/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.33/0.99    inference(nnf_transformation,[],[f21])).
% 3.33/0.99  
% 3.33/0.99  fof(f26,plain,(
% 3.33/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.33/0.99    inference(rectify,[],[f25])).
% 3.33/0.99  
% 3.33/0.99  fof(f27,plain,(
% 3.33/0.99    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v3_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.33/0.99    introduced(choice_axiom,[])).
% 3.33/0.99  
% 3.33/0.99  fof(f28,plain,(
% 3.33/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v3_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.33/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.33/0.99  
% 3.33/0.99  fof(f42,plain,(
% 3.33/0.99    ( ! [X4,X2,X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.33/0.99    inference(cnf_transformation,[],[f28])).
% 3.33/0.99  
% 3.33/0.99  fof(f58,plain,(
% 3.33/0.99    v1_funct_1(sK4)),
% 3.33/0.99    inference(cnf_transformation,[],[f33])).
% 3.33/0.99  
% 3.33/0.99  fof(f60,plain,(
% 3.33/0.99    v5_pre_topc(sK4,sK2,sK3)),
% 3.33/0.99    inference(cnf_transformation,[],[f33])).
% 3.33/0.99  
% 3.33/0.99  fof(f59,plain,(
% 3.33/0.99    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.33/0.99    inference(cnf_transformation,[],[f33])).
% 3.33/0.99  
% 3.33/0.99  fof(f61,plain,(
% 3.33/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.33/0.99    inference(cnf_transformation,[],[f33])).
% 3.33/0.99  
% 3.33/0.99  fof(f2,axiom,(
% 3.33/0.99    v1_xboole_0(k1_xboole_0)),
% 3.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.99  
% 3.33/0.99  fof(f35,plain,(
% 3.33/0.99    v1_xboole_0(k1_xboole_0)),
% 3.33/0.99    inference(cnf_transformation,[],[f2])).
% 3.33/0.99  
% 3.33/0.99  fof(f7,axiom,(
% 3.33/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.99  
% 3.33/0.99  fof(f18,plain,(
% 3.33/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.33/0.99    inference(ennf_transformation,[],[f7])).
% 3.33/0.99  
% 3.33/0.99  fof(f19,plain,(
% 3.33/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.33/0.99    inference(flattening,[],[f18])).
% 3.33/0.99  
% 3.33/0.99  fof(f41,plain,(
% 3.33/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.33/0.99    inference(cnf_transformation,[],[f19])).
% 3.33/0.99  
% 3.33/0.99  fof(f54,plain,(
% 3.33/0.99    ~v2_struct_0(sK3)),
% 3.33/0.99    inference(cnf_transformation,[],[f33])).
% 3.33/0.99  
% 3.33/0.99  fof(f3,axiom,(
% 3.33/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 3.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.99  
% 3.33/0.99  fof(f14,plain,(
% 3.33/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/0.99    inference(ennf_transformation,[],[f3])).
% 3.33/0.99  
% 3.33/0.99  fof(f36,plain,(
% 3.33/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/0.99    inference(cnf_transformation,[],[f14])).
% 3.33/0.99  
% 3.33/0.99  fof(f5,axiom,(
% 3.33/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 3.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.99  
% 3.33/0.99  fof(f16,plain,(
% 3.33/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.33/0.99    inference(ennf_transformation,[],[f5])).
% 3.33/0.99  
% 3.33/0.99  fof(f24,plain,(
% 3.33/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.33/0.99    inference(nnf_transformation,[],[f16])).
% 3.33/0.99  
% 3.33/0.99  fof(f38,plain,(
% 3.33/0.99    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.33/0.99    inference(cnf_transformation,[],[f24])).
% 3.33/0.99  
% 3.33/0.99  fof(f1,axiom,(
% 3.33/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.99  
% 3.33/0.99  fof(f11,plain,(
% 3.33/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.33/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 3.33/0.99  
% 3.33/0.99  fof(f13,plain,(
% 3.33/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 3.33/0.99    inference(ennf_transformation,[],[f11])).
% 3.33/0.99  
% 3.33/0.99  fof(f34,plain,(
% 3.33/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 3.33/0.99    inference(cnf_transformation,[],[f13])).
% 3.33/0.99  
% 3.33/0.99  fof(f57,plain,(
% 3.33/0.99    r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))),
% 3.33/0.99    inference(cnf_transformation,[],[f33])).
% 3.33/0.99  
% 3.33/0.99  fof(f39,plain,(
% 3.33/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.33/0.99    inference(cnf_transformation,[],[f24])).
% 3.33/0.99  
% 3.33/0.99  fof(f48,plain,(
% 3.33/0.99    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.33/0.99    inference(cnf_transformation,[],[f28])).
% 3.33/0.99  
% 3.33/0.99  fof(f62,plain,(
% 3.33/0.99    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 3.33/0.99    inference(cnf_transformation,[],[f33])).
% 3.33/0.99  
% 3.33/0.99  fof(f44,plain,(
% 3.33/0.99    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.33/0.99    inference(cnf_transformation,[],[f28])).
% 3.33/0.99  
% 3.33/0.99  fof(f46,plain,(
% 3.33/0.99    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v3_pre_topc(sK0(X0,X1,X2),X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.33/0.99    inference(cnf_transformation,[],[f28])).
% 3.33/0.99  
% 3.33/0.99  cnf(c_23,negated_conjecture,
% 3.33/0.99      ( l1_pre_topc(sK3) ),
% 3.33/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2452,negated_conjecture,
% 3.33/0.99      ( l1_pre_topc(sK3) ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2855,plain,
% 3.33/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2452]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_6,plain,
% 3.33/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.33/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3,plain,
% 3.33/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.33/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_353,plain,
% 3.33/0.99      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.33/0.99      inference(resolution,[status(thm)],[c_6,c_3]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2447,plain,
% 3.33/0.99      ( ~ l1_pre_topc(X0_53) | u1_struct_0(X0_53) = k2_struct_0(X0_53) ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_353]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2860,plain,
% 3.33/0.99      ( u1_struct_0(X0_53) = k2_struct_0(X0_53)
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2447]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3692,plain,
% 3.33/0.99      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_2855,c_2860]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_27,negated_conjecture,
% 3.33/0.99      ( l1_pre_topc(sK1) ),
% 3.33/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2450,negated_conjecture,
% 3.33/0.99      ( l1_pre_topc(sK1) ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_27]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2857,plain,
% 3.33/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2450]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3694,plain,
% 3.33/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_2857,c_2860]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_25,negated_conjecture,
% 3.33/0.99      ( l1_pre_topc(sK2) ),
% 3.33/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2451,negated_conjecture,
% 3.33/0.99      ( l1_pre_topc(sK2) ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2856,plain,
% 3.33/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2451]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3693,plain,
% 3.33/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_2856,c_2860]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_22,negated_conjecture,
% 3.33/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK2) ),
% 3.33/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2453,negated_conjecture,
% 3.33/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK2) ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3983,plain,
% 3.33/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK2) ),
% 3.33/0.99      inference(demodulation,[status(thm)],[c_3693,c_2453]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_4269,plain,
% 3.33/0.99      ( k2_struct_0(sK2) = k2_struct_0(sK1) ),
% 3.33/0.99      inference(demodulation,[status(thm)],[c_3694,c_3983]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_4404,plain,
% 3.33/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK1) ),
% 3.33/0.99      inference(demodulation,[status(thm)],[c_4269,c_3693]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_15,plain,
% 3.33/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.33/0.99      | ~ v5_pre_topc(X0,X1,X2)
% 3.33/0.99      | ~ v3_pre_topc(X3,X2)
% 3.33/0.99      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.33/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 3.33/0.99      | ~ v1_funct_1(X0)
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | ~ l1_pre_topc(X2)
% 3.33/0.99      | k2_struct_0(X2) = k1_xboole_0 ),
% 3.33/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_20,negated_conjecture,
% 3.33/0.99      ( v1_funct_1(sK4) ),
% 3.33/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_398,plain,
% 3.33/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.33/0.99      | ~ v5_pre_topc(X0,X1,X2)
% 3.33/0.99      | ~ v3_pre_topc(X3,X2)
% 3.33/0.99      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.33/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 3.33/0.99      | ~ l1_pre_topc(X2)
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | k2_struct_0(X2) = k1_xboole_0
% 3.33/0.99      | sK4 != X0 ),
% 3.33/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_399,plain,
% 3.33/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 3.33/0.99      | ~ v5_pre_topc(sK4,X0,X1)
% 3.33/0.99      | ~ v3_pre_topc(X2,X1)
% 3.33/0.99      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2),X0)
% 3.33/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | ~ l1_pre_topc(X0)
% 3.33/0.99      | k2_struct_0(X1) = k1_xboole_0 ),
% 3.33/0.99      inference(unflattening,[status(thm)],[c_398]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2443,plain,
% 3.33/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.33/0.99      | ~ v5_pre_topc(sK4,X0_53,X1_53)
% 3.33/0.99      | ~ v3_pre_topc(X0_51,X1_53)
% 3.33/0.99      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK4,X0_51),X0_53)
% 3.33/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X1_53)))
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.33/0.99      | ~ l1_pre_topc(X1_53)
% 3.33/0.99      | ~ l1_pre_topc(X0_53)
% 3.33/0.99      | k2_struct_0(X1_53) = k1_xboole_0 ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_399]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2861,plain,
% 3.33/0.99      ( k2_struct_0(X0_53) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,u1_struct_0(X1_53),u1_struct_0(X0_53)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,X1_53,X0_53) != iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,X0_53) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(u1_struct_0(X1_53),u1_struct_0(X0_53),sK4,X0_51),X1_53) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X0_53)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X1_53) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2443]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_5826,plain,
% 3.33/0.99      ( k2_struct_0(X0_53) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK2,X0_53) != iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,X0_53) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_53),sK4,X0_51),sK2) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_4404,c_2861]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_5845,plain,
% 3.33/0.99      ( k2_struct_0(X0_53) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(X0_53)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK2,X0_53) != iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,X0_53) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_53),sK4,X0_51),sK2) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.99      inference(light_normalisation,[status(thm)],[c_5826,c_4404]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_32,plain,
% 3.33/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_9500,plain,
% 3.33/0.99      ( l1_pre_topc(X0_53) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_53),sK4,X0_51),sK2) = iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,X0_53) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK2,X0_53) != iProver_top
% 3.33/0.99      | v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(X0_53)) != iProver_top
% 3.33/0.99      | k2_struct_0(X0_53) = k1_xboole_0 ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_5845,c_32]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_9501,plain,
% 3.33/0.99      ( k2_struct_0(X0_53) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(X0_53)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK2,X0_53) != iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,X0_53) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_53),sK4,X0_51),sK2) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 3.33/0.99      inference(renaming,[status(thm)],[c_9500]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_9515,plain,
% 3.33/0.99      ( k2_struct_0(sK3) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK2) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_3692,c_9501]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_9552,plain,
% 3.33/0.99      ( k2_struct_0(sK3) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK2) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.33/0.99      inference(light_normalisation,[status(thm)],[c_9515,c_3692]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_18,negated_conjecture,
% 3.33/0.99      ( v5_pre_topc(sK4,sK2,sK3) ),
% 3.33/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_38,plain,
% 3.33/0.99      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_19,negated_conjecture,
% 3.33/0.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.33/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2454,negated_conjecture,
% 3.33/0.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2854,plain,
% 3.33/0.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2454]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2884,plain,
% 3.33/0.99      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) = iProver_top ),
% 3.33/0.99      inference(light_normalisation,[status(thm)],[c_2854,c_2453]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3844,plain,
% 3.33/0.99      ( v1_funct_2(sK4,u1_struct_0(sK1),k2_struct_0(sK3)) = iProver_top ),
% 3.33/0.99      inference(demodulation,[status(thm)],[c_3692,c_2884]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_4480,plain,
% 3.33/0.99      ( v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3)) = iProver_top ),
% 3.33/0.99      inference(light_normalisation,[status(thm)],[c_3844,c_3694]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_17,negated_conjecture,
% 3.33/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.33/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2456,negated_conjecture,
% 3.33/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2852,plain,
% 3.33/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2456]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2887,plain,
% 3.33/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) = iProver_top ),
% 3.33/0.99      inference(light_normalisation,[status(thm)],[c_2852,c_2453]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3843,plain,
% 3.33/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK3)))) = iProver_top ),
% 3.33/0.99      inference(demodulation,[status(thm)],[c_3692,c_2887]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_4484,plain,
% 3.33/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) = iProver_top ),
% 3.33/0.99      inference(light_normalisation,[status(thm)],[c_3843,c_3694]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_4576,plain,
% 3.33/0.99      ( k2_struct_0(sK3) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,X0_53,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,X0_51),X0_53) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_3692,c_2861]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_4586,plain,
% 3.33/0.99      ( k2_struct_0(sK3) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,u1_struct_0(X0_53),k2_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,X0_53,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,X0_51),X0_53) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),k2_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.33/0.99      inference(light_normalisation,[status(thm)],[c_4576,c_3692]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_34,plain,
% 3.33/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2462,plain,( X0_52 = X0_52 ),theory(equality) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2483,plain,
% 3.33/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_2462]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2505,plain,
% 3.33/0.99      ( ~ l1_pre_topc(sK3) | u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_2447]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1,plain,
% 3.33/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.33/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_7,plain,
% 3.33/0.99      ( v2_struct_0(X0)
% 3.33/0.99      | ~ l1_struct_0(X0)
% 3.33/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.33/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_321,plain,
% 3.33/0.99      ( v2_struct_0(X0)
% 3.33/0.99      | ~ l1_struct_0(X0)
% 3.33/0.99      | u1_struct_0(X0) != k1_xboole_0 ),
% 3.33/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_339,plain,
% 3.33/0.99      ( v2_struct_0(X0)
% 3.33/0.99      | ~ l1_pre_topc(X0)
% 3.33/0.99      | u1_struct_0(X0) != k1_xboole_0 ),
% 3.33/0.99      inference(resolution,[status(thm)],[c_6,c_321]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_24,negated_conjecture,
% 3.33/0.99      ( ~ v2_struct_0(sK3) ),
% 3.33/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_371,plain,
% 3.33/0.99      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) != k1_xboole_0 | sK3 != X0 ),
% 3.33/0.99      inference(resolution_lifted,[status(thm)],[c_339,c_24]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_372,plain,
% 3.33/0.99      ( ~ l1_pre_topc(sK3) | u1_struct_0(sK3) != k1_xboole_0 ),
% 3.33/0.99      inference(unflattening,[status(thm)],[c_371]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_374,plain,
% 3.33/0.99      ( u1_struct_0(sK3) != k1_xboole_0 ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_372,c_23]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2446,plain,
% 3.33/0.99      ( u1_struct_0(sK3) != k1_xboole_0 ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_374]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2464,plain,
% 3.33/0.99      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 3.33/0.99      theory(equality) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3100,plain,
% 3.33/0.99      ( u1_struct_0(sK3) != X0_52
% 3.33/0.99      | u1_struct_0(sK3) = k1_xboole_0
% 3.33/0.99      | k1_xboole_0 != X0_52 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_2464]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3171,plain,
% 3.33/0.99      ( u1_struct_0(sK3) != k2_struct_0(sK3)
% 3.33/0.99      | u1_struct_0(sK3) = k1_xboole_0
% 3.33/0.99      | k1_xboole_0 != k2_struct_0(sK3) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_3100]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3356,plain,
% 3.33/0.99      ( k2_struct_0(sK3) != X0_52
% 3.33/0.99      | k1_xboole_0 != X0_52
% 3.33/0.99      | k1_xboole_0 = k2_struct_0(sK3) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_2464]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3357,plain,
% 3.33/0.99      ( k2_struct_0(sK3) != k1_xboole_0
% 3.33/0.99      | k1_xboole_0 = k2_struct_0(sK3)
% 3.33/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_3356]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_7918,plain,
% 3.33/0.99      ( l1_pre_topc(X0_53) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),k2_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,X0_51),X0_53) = iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,sK3) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,X0_53,sK3) != iProver_top
% 3.33/0.99      | v1_funct_2(sK4,u1_struct_0(X0_53),k2_struct_0(sK3)) != iProver_top ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_4586,c_23,c_34,c_2483,c_2505,c_2446,c_3171,c_3357]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_7919,plain,
% 3.33/0.99      ( v1_funct_2(sK4,u1_struct_0(X0_53),k2_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,X0_53,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,X0_51),X0_53) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),k2_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 3.33/0.99      inference(renaming,[status(thm)],[c_7918]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_7933,plain,
% 3.33/0.99      ( v1_funct_2(sK4,u1_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK2) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k2_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_4404,c_7919]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_7941,plain,
% 3.33/0.99      ( v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK2) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.99      inference(light_normalisation,[status(thm)],[c_7933,c_4404]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_9652,plain,
% 3.33/0.99      ( v3_pre_topc(X0_51,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK2) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_9552,c_32,c_38,c_4480,c_4484,c_7941]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2,plain,
% 3.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/0.99      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 3.33/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2459,plain,
% 3.33/0.99      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.33/0.99      | m1_subset_1(k8_relset_1(X0_52,X1_52,X0_51,X1_51),k1_zfmisc_1(X0_52)) ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2849,plain,
% 3.33/0.99      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.33/0.99      | m1_subset_1(k8_relset_1(X0_52,X1_52,X0_51,X1_51),k1_zfmisc_1(X0_52)) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2459]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_5,plain,
% 3.33/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | r2_hidden(X0,u1_pre_topc(X1))
% 3.33/0.99      | ~ l1_pre_topc(X1) ),
% 3.33/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2457,plain,
% 3.33/0.99      ( ~ v3_pre_topc(X0_51,X0_53)
% 3.33/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53)))
% 3.33/0.99      | r2_hidden(X0_51,u1_pre_topc(X0_53))
% 3.33/0.99      | ~ l1_pre_topc(X0_53) ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2851,plain,
% 3.33/0.99      ( v3_pre_topc(X0_51,X0_53) != iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 3.33/0.99      | r2_hidden(X0_51,u1_pre_topc(X0_53)) = iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2457]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3302,plain,
% 3.33/0.99      ( v3_pre_topc(X0_51,sK2) != iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.33/0.99      | r2_hidden(X0_51,u1_pre_topc(sK2)) = iProver_top
% 3.33/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_2453,c_2851]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3374,plain,
% 3.33/0.99      ( r2_hidden(X0_51,u1_pre_topc(sK2)) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,sK2) != iProver_top ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_3302,c_32]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3375,plain,
% 3.33/0.99      ( v3_pre_topc(X0_51,sK2) != iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.33/0.99      | r2_hidden(X0_51,u1_pre_topc(sK2)) = iProver_top ),
% 3.33/0.99      inference(renaming,[status(thm)],[c_3374]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3383,plain,
% 3.33/0.99      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK1),X0_52,X0_51,X1_51),sK2) != iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_52))) != iProver_top
% 3.33/0.99      | r2_hidden(k8_relset_1(u1_struct_0(sK1),X0_52,X0_51,X1_51),u1_pre_topc(sK2)) = iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_2849,c_3375]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_0,plain,
% 3.33/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.33/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_21,negated_conjecture,
% 3.33/0.99      ( r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) ),
% 3.33/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_306,plain,
% 3.33/0.99      ( ~ r2_hidden(X0,X1)
% 3.33/0.99      | r2_hidden(X0,X2)
% 3.33/0.99      | u1_pre_topc(sK2) != X1
% 3.33/0.99      | u1_pre_topc(sK1) != X2 ),
% 3.33/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_307,plain,
% 3.33/0.99      ( ~ r2_hidden(X0,u1_pre_topc(sK2))
% 3.33/0.99      | r2_hidden(X0,u1_pre_topc(sK1)) ),
% 3.33/0.99      inference(unflattening,[status(thm)],[c_306]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2448,plain,
% 3.33/0.99      ( ~ r2_hidden(X0_51,u1_pre_topc(sK2))
% 3.33/0.99      | r2_hidden(X0_51,u1_pre_topc(sK1)) ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_307]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2859,plain,
% 3.33/0.99      ( r2_hidden(X0_51,u1_pre_topc(sK2)) != iProver_top
% 3.33/0.99      | r2_hidden(X0_51,u1_pre_topc(sK1)) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2448]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3484,plain,
% 3.33/0.99      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK1),X0_52,X0_51,X1_51),sK2) != iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0_52))) != iProver_top
% 3.33/0.99      | r2_hidden(k8_relset_1(u1_struct_0(sK1),X0_52,X0_51,X1_51),u1_pre_topc(sK1)) = iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_3383,c_2859]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_6002,plain,
% 3.33/0.99      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK1),X0_52,X0_51,X1_51),sK2) != iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X0_52))) != iProver_top
% 3.33/0.99      | r2_hidden(k8_relset_1(k2_struct_0(sK1),X0_52,X0_51,X1_51),u1_pre_topc(sK1)) = iProver_top ),
% 3.33/0.99      inference(light_normalisation,[status(thm)],[c_3484,c_3694]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_4,plain,
% 3.33/0.99      ( v3_pre_topc(X0,X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.33/0.99      | ~ l1_pre_topc(X1) ),
% 3.33/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2458,plain,
% 3.33/0.99      ( v3_pre_topc(X0_51,X0_53)
% 3.33/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53)))
% 3.33/0.99      | ~ r2_hidden(X0_51,u1_pre_topc(X0_53))
% 3.33/0.99      | ~ l1_pre_topc(X0_53) ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2850,plain,
% 3.33/0.99      ( v3_pre_topc(X0_51,X0_53) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 3.33/0.99      | r2_hidden(X0_51,u1_pre_topc(X0_53)) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2458]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_4156,plain,
% 3.33/0.99      ( v3_pre_topc(X0_51,sK1) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 3.33/0.99      | r2_hidden(X0_51,u1_pre_topc(sK1)) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_3983,c_2850]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_30,plain,
% 3.33/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_5021,plain,
% 3.33/0.99      ( r2_hidden(X0_51,u1_pre_topc(sK1)) != iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,sK1) = iProver_top ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_4156,c_30]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_5022,plain,
% 3.33/0.99      ( v3_pre_topc(X0_51,sK1) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 3.33/0.99      | r2_hidden(X0_51,u1_pre_topc(sK1)) != iProver_top ),
% 3.33/0.99      inference(renaming,[status(thm)],[c_5021]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_5027,plain,
% 3.33/0.99      ( v3_pre_topc(X0_51,sK1) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 3.33/0.99      | r2_hidden(X0_51,u1_pre_topc(sK1)) != iProver_top ),
% 3.33/0.99      inference(light_normalisation,[status(thm)],[c_5022,c_4269]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_5034,plain,
% 3.33/0.99      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK1),X0_52,X0_51,X1_51),sK1) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X0_52))) != iProver_top
% 3.33/0.99      | r2_hidden(k8_relset_1(k2_struct_0(sK1),X0_52,X0_51,X1_51),u1_pre_topc(sK1)) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_2849,c_5027]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_6857,plain,
% 3.33/0.99      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK1),X0_52,X0_51,X1_51),sK2) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),X0_52,X0_51,X1_51),sK1) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X0_52))) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_6002,c_5034]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_9661,plain,
% 3.33/0.99      ( v3_pre_topc(X0_51,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK1) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_9652,c_6857]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_9813,plain,
% 3.33/0.99      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK1) = iProver_top
% 3.33/0.99      | v3_pre_topc(X0_51,sK3) != iProver_top ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_9661,c_4484]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_9814,plain,
% 3.33/0.99      ( v3_pre_topc(X0_51,sK3) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0_51),sK1) = iProver_top
% 3.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.33/0.99      inference(renaming,[status(thm)],[c_9813]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_9,plain,
% 3.33/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.33/0.99      | v5_pre_topc(X0,X1,X2)
% 3.33/0.99      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.33/0.99      | ~ v1_funct_1(X0)
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | ~ l1_pre_topc(X2)
% 3.33/0.99      | k2_struct_0(X2) = k1_xboole_0 ),
% 3.33/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_572,plain,
% 3.33/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.33/0.99      | v5_pre_topc(X0,X1,X2)
% 3.33/0.99      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.33/0.99      | ~ l1_pre_topc(X2)
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | k2_struct_0(X2) = k1_xboole_0
% 3.33/0.99      | sK4 != X0 ),
% 3.33/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_573,plain,
% 3.33/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 3.33/0.99      | v5_pre_topc(sK4,X0,X1)
% 3.33/0.99      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK0(X0,X1,sK4)),X0)
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | ~ l1_pre_topc(X0)
% 3.33/0.99      | k2_struct_0(X1) = k1_xboole_0 ),
% 3.33/0.99      inference(unflattening,[status(thm)],[c_572]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2437,plain,
% 3.33/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.33/0.99      | v5_pre_topc(sK4,X0_53,X1_53)
% 3.33/0.99      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK4,sK0(X0_53,X1_53,sK4)),X0_53)
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.33/0.99      | ~ l1_pre_topc(X1_53)
% 3.33/0.99      | ~ l1_pre_topc(X0_53)
% 3.33/0.99      | k2_struct_0(X1_53) = k1_xboole_0 ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_573]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2867,plain,
% 3.33/0.99      ( k2_struct_0(X0_53) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,u1_struct_0(X1_53),u1_struct_0(X0_53)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,X1_53,X0_53) = iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(u1_struct_0(X1_53),u1_struct_0(X0_53),sK4,sK0(X1_53,X0_53,sK4)),X1_53) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X0_53)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X1_53) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2437]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_5638,plain,
% 3.33/0.99      ( k2_struct_0(sK3) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,X0_53,sK3) = iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,sK0(X0_53,sK3,sK4)),X0_53) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_3692,c_2867]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_5646,plain,
% 3.33/0.99      ( k2_struct_0(sK3) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,u1_struct_0(X0_53),k2_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,X0_53,sK3) = iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,sK0(X0_53,sK3,sK4)),X0_53) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),k2_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.33/0.99      inference(light_normalisation,[status(thm)],[c_5638,c_3692]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_7971,plain,
% 3.33/0.99      ( l1_pre_topc(X0_53) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),k2_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,sK0(X0_53,sK3,sK4)),X0_53) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,X0_53,sK3) = iProver_top
% 3.33/0.99      | v1_funct_2(sK4,u1_struct_0(X0_53),k2_struct_0(sK3)) != iProver_top ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_5646,c_23,c_34,c_2483,c_2505,c_2446,c_3171,c_3357]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_7972,plain,
% 3.33/0.99      ( v1_funct_2(sK4,u1_struct_0(X0_53),k2_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,X0_53,sK3) = iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_53),k2_struct_0(sK3),sK4,sK0(X0_53,sK3,sK4)),X0_53) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),k2_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 3.33/0.99      inference(renaming,[status(thm)],[c_7971]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_7983,plain,
% 3.33/0.99      ( v1_funct_2(sK4,u1_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK1,sK3) = iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,sK0(sK1,sK3,sK4)),sK1) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_3694,c_7972]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_8002,plain,
% 3.33/0.99      ( v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK1,sK3) = iProver_top
% 3.33/0.99      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,sK0(sK1,sK3,sK4)),sK1) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.33/0.99      inference(light_normalisation,[status(thm)],[c_7983,c_3694]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_16,negated_conjecture,
% 3.33/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
% 3.33/0.99      | ~ v5_pre_topc(sK4,sK1,sK3)
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
% 3.33/0.99      | ~ v1_funct_1(sK4) ),
% 3.33/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_153,plain,
% 3.33/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
% 3.33/0.99      | ~ v5_pre_topc(sK4,sK1,sK3)
% 3.33/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_16,c_20]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_154,negated_conjecture,
% 3.33/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
% 3.33/0.99      | ~ v5_pre_topc(sK4,sK1,sK3)
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) ),
% 3.33/0.99      inference(renaming,[status(thm)],[c_153]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2449,negated_conjecture,
% 3.33/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
% 3.33/0.99      | ~ v5_pre_topc(sK4,sK1,sK3)
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_154]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2858,plain,
% 3.33/0.99      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK1,sK3) != iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) != iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2449]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2921,plain,
% 3.33/0.99      ( v5_pre_topc(sK4,sK1,sK3) != iProver_top ),
% 3.33/0.99      inference(forward_subsumption_resolution,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_2858,c_2887,c_2884]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_8170,plain,
% 3.33/0.99      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,sK0(sK1,sK3,sK4)),sK1) != iProver_top ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_8002,c_30,c_2921,c_4480,c_4484]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_9822,plain,
% 3.33/0.99      ( v3_pre_topc(sK0(sK1,sK3,sK4),sK3) != iProver_top
% 3.33/0.99      | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_9814,c_8170]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2467,plain,
% 3.33/0.99      ( ~ m1_subset_1(X0_51,X0_54)
% 3.33/0.99      | m1_subset_1(X1_51,X1_54)
% 3.33/0.99      | X1_54 != X0_54
% 3.33/0.99      | X1_51 != X0_51 ),
% 3.33/0.99      theory(equality) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3262,plain,
% 3.33/0.99      ( m1_subset_1(X0_51,X0_54)
% 3.33/0.99      | ~ m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(u1_struct_0(X0_53)))
% 3.33/0.99      | X0_54 != k1_zfmisc_1(u1_struct_0(X0_53))
% 3.33/0.99      | X0_51 != sK0(sK1,X0_53,sK4) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_2467]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3564,plain,
% 3.33/0.99      ( m1_subset_1(X0_51,k1_zfmisc_1(X0_52))
% 3.33/0.99      | ~ m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(u1_struct_0(X0_53)))
% 3.33/0.99      | k1_zfmisc_1(X0_52) != k1_zfmisc_1(u1_struct_0(X0_53))
% 3.33/0.99      | X0_51 != sK0(sK1,X0_53,sK4) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_3262]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_5061,plain,
% 3.33/0.99      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(X0_53)))
% 3.33/0.99      | ~ m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(u1_struct_0(X0_53)))
% 3.33/0.99      | k1_zfmisc_1(k2_struct_0(X0_53)) != k1_zfmisc_1(u1_struct_0(X0_53))
% 3.33/0.99      | X0_51 != sK0(sK1,X0_53,sK4) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_3564]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_6654,plain,
% 3.33/0.99      ( ~ m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(u1_struct_0(X0_53)))
% 3.33/0.99      | m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(k2_struct_0(X0_53)))
% 3.33/0.99      | k1_zfmisc_1(k2_struct_0(X0_53)) != k1_zfmisc_1(u1_struct_0(X0_53))
% 3.33/0.99      | sK0(sK1,X0_53,sK4) != sK0(sK1,X0_53,sK4) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_5061]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_6656,plain,
% 3.33/0.99      ( k1_zfmisc_1(k2_struct_0(X0_53)) != k1_zfmisc_1(u1_struct_0(X0_53))
% 3.33/0.99      | sK0(sK1,X0_53,sK4) != sK0(sK1,X0_53,sK4)
% 3.33/0.99      | m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 3.33/0.99      | m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(k2_struct_0(X0_53))) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_6654]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_6658,plain,
% 3.33/0.99      ( k1_zfmisc_1(k2_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
% 3.33/0.99      | sK0(sK1,sK3,sK4) != sK0(sK1,sK3,sK4)
% 3.33/0.99      | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.33/0.99      | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_6656]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2466,plain,
% 3.33/0.99      ( k1_zfmisc_1(X0_52) = k1_zfmisc_1(X1_52) | X0_52 != X1_52 ),
% 3.33/0.99      theory(equality) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3565,plain,
% 3.33/0.99      ( k1_zfmisc_1(X0_52) = k1_zfmisc_1(u1_struct_0(X0_53))
% 3.33/0.99      | X0_52 != u1_struct_0(X0_53) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_2466]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_4438,plain,
% 3.33/0.99      ( k1_zfmisc_1(k2_struct_0(X0_53)) = k1_zfmisc_1(u1_struct_0(X0_53))
% 3.33/0.99      | k2_struct_0(X0_53) != u1_struct_0(X0_53) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_3565]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_4442,plain,
% 3.33/0.99      ( k1_zfmisc_1(k2_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3))
% 3.33/0.99      | k2_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_4438]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3182,plain,
% 3.33/0.99      ( X0_52 != X1_52
% 3.33/0.99      | k2_struct_0(X0_53) != X1_52
% 3.33/0.99      | k2_struct_0(X0_53) = X0_52 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_2464]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3419,plain,
% 3.33/0.99      ( X0_52 != k2_struct_0(X0_53)
% 3.33/0.99      | k2_struct_0(X0_53) = X0_52
% 3.33/0.99      | k2_struct_0(X0_53) != k2_struct_0(X0_53) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_3182]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3701,plain,
% 3.33/0.99      ( u1_struct_0(X0_53) != k2_struct_0(X0_53)
% 3.33/0.99      | k2_struct_0(X0_53) = u1_struct_0(X0_53)
% 3.33/0.99      | k2_struct_0(X0_53) != k2_struct_0(X0_53) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_3419]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3702,plain,
% 3.33/0.99      ( u1_struct_0(sK3) != k2_struct_0(sK3)
% 3.33/0.99      | k2_struct_0(sK3) = u1_struct_0(sK3)
% 3.33/0.99      | k2_struct_0(sK3) != k2_struct_0(sK3) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_3701]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2471,plain,
% 3.33/0.99      ( X0_51 != X1_51
% 3.33/0.99      | sK0(X0_53,X1_53,X0_51) = sK0(X0_53,X1_53,X1_51) ),
% 3.33/0.99      theory(equality) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3542,plain,
% 3.33/0.99      ( X0_51 != sK4 | sK0(sK1,X0_53,X0_51) = sK0(sK1,X0_53,sK4) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_2471]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3545,plain,
% 3.33/0.99      ( sK0(sK1,sK3,sK4) = sK0(sK1,sK3,sK4) | sK4 != sK4 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_3542]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_13,plain,
% 3.33/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.33/0.99      | v5_pre_topc(X0,X1,X2)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.33/0.99      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 3.33/0.99      | ~ v1_funct_1(X0)
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | ~ l1_pre_topc(X2)
% 3.33/0.99      | k2_struct_0(X2) = k1_xboole_0 ),
% 3.33/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_464,plain,
% 3.33/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.33/0.99      | v5_pre_topc(X0,X1,X2)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.33/0.99      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 3.33/0.99      | ~ l1_pre_topc(X2)
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | k2_struct_0(X2) = k1_xboole_0
% 3.33/0.99      | sK4 != X0 ),
% 3.33/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_465,plain,
% 3.33/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 3.33/0.99      | v5_pre_topc(sK4,X0,X1)
% 3.33/0.99      | m1_subset_1(sK0(X0,X1,sK4),k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | ~ l1_pre_topc(X0)
% 3.33/0.99      | k2_struct_0(X1) = k1_xboole_0 ),
% 3.33/0.99      inference(unflattening,[status(thm)],[c_464]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2441,plain,
% 3.33/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.33/0.99      | v5_pre_topc(sK4,X0_53,X1_53)
% 3.33/0.99      | m1_subset_1(sK0(X0_53,X1_53,sK4),k1_zfmisc_1(u1_struct_0(X1_53)))
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.33/0.99      | ~ l1_pre_topc(X1_53)
% 3.33/0.99      | ~ l1_pre_topc(X0_53)
% 3.33/0.99      | k2_struct_0(X1_53) = k1_xboole_0 ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_465]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3186,plain,
% 3.33/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0_53))
% 3.33/0.99      | v5_pre_topc(sK4,sK1,X0_53)
% 3.33/0.99      | m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(u1_struct_0(X0_53)))
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53))))
% 3.33/0.99      | ~ l1_pre_topc(X0_53)
% 3.33/0.99      | ~ l1_pre_topc(sK1)
% 3.33/0.99      | k2_struct_0(X0_53) = k1_xboole_0 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_2441]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3194,plain,
% 3.33/0.99      ( k2_struct_0(X0_53) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0_53)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK1,X0_53) = iProver_top
% 3.33/0.99      | m1_subset_1(sK0(sK1,X0_53,sK4),k1_zfmisc_1(u1_struct_0(X0_53))) = iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_3186]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3196,plain,
% 3.33/0.99      ( k2_struct_0(sK3) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK1,sK3) = iProver_top
% 3.33/0.99      | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_3194]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_11,plain,
% 3.33/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.33/0.99      | v5_pre_topc(X0,X1,X2)
% 3.33/0.99      | v3_pre_topc(sK0(X1,X2,X0),X2)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.33/0.99      | ~ v1_funct_1(X0)
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | ~ l1_pre_topc(X2)
% 3.33/0.99      | k2_struct_0(X2) = k1_xboole_0 ),
% 3.33/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_518,plain,
% 3.33/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.33/0.99      | v5_pre_topc(X0,X1,X2)
% 3.33/0.99      | v3_pre_topc(sK0(X1,X2,X0),X2)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.33/0.99      | ~ l1_pre_topc(X2)
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | k2_struct_0(X2) = k1_xboole_0
% 3.33/0.99      | sK4 != X0 ),
% 3.33/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_519,plain,
% 3.33/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 3.33/0.99      | v5_pre_topc(sK4,X0,X1)
% 3.33/0.99      | v3_pre_topc(sK0(X0,X1,sK4),X1)
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | ~ l1_pre_topc(X0)
% 3.33/0.99      | k2_struct_0(X1) = k1_xboole_0 ),
% 3.33/0.99      inference(unflattening,[status(thm)],[c_518]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2439,plain,
% 3.33/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.33/0.99      | v5_pre_topc(sK4,X0_53,X1_53)
% 3.33/0.99      | v3_pre_topc(sK0(X0_53,X1_53,sK4),X1_53)
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.33/0.99      | ~ l1_pre_topc(X1_53)
% 3.33/0.99      | ~ l1_pre_topc(X0_53)
% 3.33/0.99      | k2_struct_0(X1_53) = k1_xboole_0 ),
% 3.33/0.99      inference(subtyping,[status(esa)],[c_519]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3187,plain,
% 3.33/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0_53))
% 3.33/0.99      | v5_pre_topc(sK4,sK1,X0_53)
% 3.33/0.99      | v3_pre_topc(sK0(sK1,X0_53,sK4),X0_53)
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53))))
% 3.33/0.99      | ~ l1_pre_topc(X0_53)
% 3.33/0.99      | ~ l1_pre_topc(sK1)
% 3.33/0.99      | k2_struct_0(X0_53) = k1_xboole_0 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_2439]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3190,plain,
% 3.33/0.99      ( k2_struct_0(X0_53) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0_53)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK1,X0_53) = iProver_top
% 3.33/0.99      | v3_pre_topc(sK0(sK1,X0_53,sK4),X0_53) = iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_53)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0_53) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_3187]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3192,plain,
% 3.33/0.99      ( k2_struct_0(sK3) = k1_xboole_0
% 3.33/0.99      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top
% 3.33/0.99      | v5_pre_topc(sK4,sK1,sK3) = iProver_top
% 3.33/0.99      | v3_pre_topc(sK0(sK1,sK3,sK4),sK3) = iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_3190]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3179,plain,
% 3.33/0.99      ( k2_struct_0(X0_53) = k2_struct_0(X0_53) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_2462]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3181,plain,
% 3.33/0.99      ( k2_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_3179]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2461,plain,( X0_51 = X0_51 ),theory(equality) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2482,plain,
% 3.33/0.99      ( sK4 = sK4 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_2461]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(contradiction,plain,
% 3.33/0.99      ( $false ),
% 3.33/0.99      inference(minisat,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_9822,c_6658,c_4442,c_3702,c_3545,c_3357,c_3196,c_3192,
% 3.33/0.99                 c_3181,c_3171,c_2884,c_2921,c_2887,c_2446,c_2505,c_2483,
% 3.33/0.99                 c_2482,c_34,c_23,c_30]) ).
% 3.33/0.99  
% 3.33/0.99  
% 3.33/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.33/0.99  
% 3.33/0.99  ------                               Statistics
% 3.33/0.99  
% 3.33/0.99  ------ General
% 3.33/0.99  
% 3.33/0.99  abstr_ref_over_cycles:                  0
% 3.33/0.99  abstr_ref_under_cycles:                 0
% 3.33/0.99  gc_basic_clause_elim:                   0
% 3.33/0.99  forced_gc_time:                         0
% 3.33/0.99  parsing_time:                           0.01
% 3.33/0.99  unif_index_cands_time:                  0.
% 3.33/0.99  unif_index_add_time:                    0.
% 3.33/0.99  orderings_time:                         0.
% 3.33/0.99  out_proof_time:                         0.014
% 3.33/0.99  total_time:                             0.287
% 3.33/0.99  num_of_symbols:                         59
% 3.33/0.99  num_of_terms:                           4532
% 3.33/0.99  
% 3.33/0.99  ------ Preprocessing
% 3.33/0.99  
% 3.33/0.99  num_of_splits:                          0
% 3.33/0.99  num_of_split_atoms:                     0
% 3.33/0.99  num_of_reused_defs:                     0
% 3.33/0.99  num_eq_ax_congr_red:                    24
% 3.33/0.99  num_of_sem_filtered_clauses:            1
% 3.33/0.99  num_of_subtypes:                        5
% 3.33/0.99  monotx_restored_types:                  0
% 3.33/0.99  sat_num_of_epr_types:                   0
% 3.33/0.99  sat_num_of_non_cyclic_types:            0
% 3.33/0.99  sat_guarded_non_collapsed_types:        0
% 3.33/0.99  num_pure_diseq_elim:                    0
% 3.33/0.99  simp_replaced_by:                       0
% 3.33/0.99  res_preprocessed:                       126
% 3.33/0.99  prep_upred:                             0
% 3.33/0.99  prep_unflattend:                        45
% 3.33/0.99  smt_new_axioms:                         0
% 3.33/0.99  pred_elim_cands:                        6
% 3.33/0.99  pred_elim:                              5
% 3.33/0.99  pred_elim_cl:                           5
% 3.33/0.99  pred_elim_cycles:                       9
% 3.33/0.99  merged_defs:                            0
% 3.33/0.99  merged_defs_ncl:                        0
% 3.33/0.99  bin_hyper_res:                          0
% 3.33/0.99  prep_cycles:                            4
% 3.33/0.99  pred_elim_time:                         0.049
% 3.33/0.99  splitting_time:                         0.
% 3.33/0.99  sem_filter_time:                        0.
% 3.33/0.99  monotx_time:                            0.
% 3.33/0.99  subtype_inf_time:                       0.
% 3.33/0.99  
% 3.33/0.99  ------ Problem properties
% 3.33/0.99  
% 3.33/0.99  clauses:                                24
% 3.33/0.99  conjectures:                            8
% 3.33/0.99  epr:                                    4
% 3.33/0.99  horn:                                   18
% 3.33/0.99  ground:                                 11
% 3.33/0.99  unary:                                  10
% 3.33/0.99  binary:                                 3
% 3.33/0.99  lits:                                   87
% 3.33/0.99  lits_eq:                                13
% 3.33/0.99  fd_pure:                                0
% 3.33/0.99  fd_pseudo:                              0
% 3.33/0.99  fd_cond:                                0
% 3.33/0.99  fd_pseudo_cond:                         0
% 3.33/0.99  ac_symbols:                             0
% 3.33/0.99  
% 3.33/0.99  ------ Propositional Solver
% 3.33/0.99  
% 3.33/0.99  prop_solver_calls:                      30
% 3.33/0.99  prop_fast_solver_calls:                 2314
% 3.33/0.99  smt_solver_calls:                       0
% 3.33/0.99  smt_fast_solver_calls:                  0
% 3.33/0.99  prop_num_of_clauses:                    2426
% 3.33/0.99  prop_preprocess_simplified:             6571
% 3.33/0.99  prop_fo_subsumed:                       150
% 3.33/0.99  prop_solver_time:                       0.
% 3.33/0.99  smt_solver_time:                        0.
% 3.33/0.99  smt_fast_solver_time:                   0.
% 3.33/0.99  prop_fast_solver_time:                  0.
% 3.33/0.99  prop_unsat_core_time:                   0.
% 3.33/0.99  
% 3.33/0.99  ------ QBF
% 3.33/0.99  
% 3.33/0.99  qbf_q_res:                              0
% 3.33/0.99  qbf_num_tautologies:                    0
% 3.33/0.99  qbf_prep_cycles:                        0
% 3.33/0.99  
% 3.33/0.99  ------ BMC1
% 3.33/0.99  
% 3.33/0.99  bmc1_current_bound:                     -1
% 3.33/0.99  bmc1_last_solved_bound:                 -1
% 3.33/0.99  bmc1_unsat_core_size:                   -1
% 3.33/0.99  bmc1_unsat_core_parents_size:           -1
% 3.33/0.99  bmc1_merge_next_fun:                    0
% 3.33/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.33/0.99  
% 3.33/0.99  ------ Instantiation
% 3.33/0.99  
% 3.33/0.99  inst_num_of_clauses:                    714
% 3.33/0.99  inst_num_in_passive:                    83
% 3.33/0.99  inst_num_in_active:                     543
% 3.33/0.99  inst_num_in_unprocessed:                88
% 3.33/0.99  inst_num_of_loops:                      560
% 3.33/0.99  inst_num_of_learning_restarts:          0
% 3.33/0.99  inst_num_moves_active_passive:          10
% 3.33/0.99  inst_lit_activity:                      0
% 3.33/0.99  inst_lit_activity_moves:                0
% 3.33/0.99  inst_num_tautologies:                   0
% 3.33/0.99  inst_num_prop_implied:                  0
% 3.33/0.99  inst_num_existing_simplified:           0
% 3.33/0.99  inst_num_eq_res_simplified:             0
% 3.33/0.99  inst_num_child_elim:                    0
% 3.33/0.99  inst_num_of_dismatching_blockings:      259
% 3.33/0.99  inst_num_of_non_proper_insts:           1067
% 3.33/0.99  inst_num_of_duplicates:                 0
% 3.33/0.99  inst_inst_num_from_inst_to_res:         0
% 3.33/0.99  inst_dismatching_checking_time:         0.
% 3.33/0.99  
% 3.33/0.99  ------ Resolution
% 3.33/0.99  
% 3.33/0.99  res_num_of_clauses:                     0
% 3.33/0.99  res_num_in_passive:                     0
% 3.33/0.99  res_num_in_active:                      0
% 3.33/0.99  res_num_of_loops:                       130
% 3.33/0.99  res_forward_subset_subsumed:            168
% 3.33/0.99  res_backward_subset_subsumed:           0
% 3.33/0.99  res_forward_subsumed:                   0
% 3.33/0.99  res_backward_subsumed:                  0
% 3.33/0.99  res_forward_subsumption_resolution:     0
% 3.33/0.99  res_backward_subsumption_resolution:    0
% 3.33/0.99  res_clause_to_clause_subsumption:       642
% 3.33/0.99  res_orphan_elimination:                 0
% 3.33/0.99  res_tautology_del:                      158
% 3.33/0.99  res_num_eq_res_simplified:              0
% 3.33/0.99  res_num_sel_changes:                    0
% 3.33/0.99  res_moves_from_active_to_pass:          0
% 3.33/0.99  
% 3.33/0.99  ------ Superposition
% 3.33/0.99  
% 3.33/0.99  sup_time_total:                         0.
% 3.33/0.99  sup_time_generating:                    0.
% 3.33/0.99  sup_time_sim_full:                      0.
% 3.33/0.99  sup_time_sim_immed:                     0.
% 3.33/0.99  
% 3.33/0.99  sup_num_of_clauses:                     116
% 3.33/0.99  sup_num_in_active:                      96
% 3.33/0.99  sup_num_in_passive:                     20
% 3.33/0.99  sup_num_of_loops:                       110
% 3.33/0.99  sup_fw_superposition:                   109
% 3.33/0.99  sup_bw_superposition:                   64
% 3.33/0.99  sup_immediate_simplified:               122
% 3.33/0.99  sup_given_eliminated:                   0
% 3.33/0.99  comparisons_done:                       0
% 3.33/0.99  comparisons_avoided:                    0
% 3.33/0.99  
% 3.33/0.99  ------ Simplifications
% 3.33/0.99  
% 3.33/0.99  
% 3.33/0.99  sim_fw_subset_subsumed:                 23
% 3.33/0.99  sim_bw_subset_subsumed:                 9
% 3.33/0.99  sim_fw_subsumed:                        27
% 3.33/0.99  sim_bw_subsumed:                        0
% 3.33/0.99  sim_fw_subsumption_res:                 2
% 3.33/0.99  sim_bw_subsumption_res:                 0
% 3.33/0.99  sim_tautology_del:                      17
% 3.33/0.99  sim_eq_tautology_del:                   0
% 3.33/0.99  sim_eq_res_simp:                        0
% 3.33/0.99  sim_fw_demodulated:                     14
% 3.33/0.99  sim_bw_demodulated:                     15
% 3.33/0.99  sim_light_normalised:                   119
% 3.33/0.99  sim_joinable_taut:                      0
% 3.33/0.99  sim_joinable_simp:                      0
% 3.33/0.99  sim_ac_normalised:                      0
% 3.33/0.99  sim_smt_subsumption:                    0
% 3.33/0.99  
%------------------------------------------------------------------------------
