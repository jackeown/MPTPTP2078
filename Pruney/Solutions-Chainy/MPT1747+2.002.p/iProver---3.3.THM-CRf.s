%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:19 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  181 (1652 expanded)
%              Number of clauses        :  125 ( 501 expanded)
%              Number of leaves         :   16 ( 501 expanded)
%              Depth                    :   20
%              Number of atoms          :  861 (18710 expanded)
%              Number of equality atoms :  300 (1793 expanded)
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
             => ( ( r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                  & u1_struct_0(X1) = u1_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v5_pre_topc(X3,X0,X1)
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
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
               => ( ( r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                    & u1_struct_0(X1) = u1_struct_0(X2) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v5_pre_topc(X3,X0,X1)
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
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
               => ( ( r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                    & u1_struct_0(X1) = u1_struct_0(X2) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v5_pre_topc(X3,X0,X1)
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
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
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X3,X0,X1)
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
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
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X3,X0,X1)
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
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
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X3,X0,X1)
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X3) )
     => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
          | ~ v5_pre_topc(sK4,X0,X2)
          | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X2))
          | ~ v1_funct_1(sK4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(sK4,X0,X1)
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
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
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X3,X0,X1)
              & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X3) )
          & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
          & u1_struct_0(X1) = u1_struct_0(X2)
          & l1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
              | ~ v5_pre_topc(X3,X0,sK3)
              | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK3))
              | ~ v1_funct_1(X3) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X3,X0,X1)
            & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X3) )
        & r1_tarski(u1_pre_topc(sK3),u1_pre_topc(X1))
        & u1_struct_0(sK3) = u1_struct_0(X1)
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
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X3,X0,X1)
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
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
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
                & v5_pre_topc(X3,X0,sK2)
                & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK2))
                & v1_funct_1(X3) )
            & r1_tarski(u1_pre_topc(X2),u1_pre_topc(sK2))
            & u1_struct_0(sK2) = u1_struct_0(X2)
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
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v5_pre_topc(X3,X0,X1)
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                & u1_struct_0(X1) = u1_struct_0(X2)
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
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
                  & v5_pre_topc(X3,sK1,X1)
                  & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
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
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v5_pre_topc(sK4,sK1,sK2)
    & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2))
    & u1_struct_0(sK2) = u1_struct_0(sK3)
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

fof(f56,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
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

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f51,plain,(
    l1_pre_topc(sK1) ),
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

fof(f62,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    v5_pre_topc(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2444,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2852,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2444])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_347,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_3])).

cnf(c_2439,plain,
    ( ~ l1_pre_topc(X0_52)
    | u1_struct_0(X0_52) = k2_struct_0(X0_52) ),
    inference(subtyping,[status(esa)],[c_347])).

cnf(c_2857,plain,
    ( u1_struct_0(X0_52) = k2_struct_0(X0_52)
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2439])).

cnf(c_3587,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2852,c_2857])).

cnf(c_22,negated_conjecture,
    ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2445,negated_conjecture,
    ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3729,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_3587,c_2445])).

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

cnf(c_392,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_393,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v5_pre_topc(sK4,X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_2435,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ v5_pre_topc(sK4,X0_52,X1_52)
    | ~ v3_pre_topc(X0_51,X1_52)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),u1_struct_0(X1_52),sK4,X0_51),X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(X1_52)
    | k2_struct_0(X1_52) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_393])).

cnf(c_2858,plain,
    ( k2_struct_0(X0_52) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v5_pre_topc(sK4,X1_52,X0_52) != iProver_top
    | v3_pre_topc(X0_51,X0_52) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1_52),u1_struct_0(X0_52),sK4,X0_51),X1_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2435])).

cnf(c_4306,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X0_52),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK2) != iProver_top
    | v3_pre_topc(X0_51,sK2) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,X0_51),X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3729,c_2858])).

cnf(c_4316,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK2) != iProver_top
    | v3_pre_topc(X0_51,sK2) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,X0_51),X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4306,c_3729])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2443,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2853,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2443])).

cnf(c_3588,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2853,c_2857])).

cnf(c_3930,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_3588,c_3729])).

cnf(c_4317,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK2) != iProver_top
    | v3_pre_topc(X0_51,sK2) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,X0_51),X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4316,c_3930])).

cnf(c_32,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2453,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_2475,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2453])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_315,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_333,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_315])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_365,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_333,c_24])).

cnf(c_366,plain,
    ( ~ l1_pre_topc(sK3)
    | u1_struct_0(sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_368,plain,
    ( u1_struct_0(sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_23])).

cnf(c_2438,plain,
    ( u1_struct_0(sK3) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_368])).

cnf(c_2455,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_3098,plain,
    ( u1_struct_0(sK3) != X0_51
    | u1_struct_0(sK3) = k1_xboole_0
    | k1_xboole_0 != X0_51 ),
    inference(instantiation,[status(thm)],[c_2455])).

cnf(c_3154,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | u1_struct_0(sK3) = k1_xboole_0
    | k1_xboole_0 != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3098])).

cnf(c_3155,plain,
    ( ~ l1_pre_topc(sK3)
    | u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2439])).

cnf(c_3258,plain,
    ( k2_struct_0(sK3) != X0_51
    | k1_xboole_0 != X0_51
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2455])).

cnf(c_3259,plain,
    ( k2_struct_0(sK3) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3258])).

cnf(c_6657,plain,
    ( l1_pre_topc(X0_52) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,X0_51),X0_52) = iProver_top
    | v3_pre_topc(X0_51,sK2) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK2) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4317,c_32,c_23,c_2475,c_2438,c_3154,c_3155,c_3259])).

cnf(c_6658,plain,
    ( v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK2) != iProver_top
    | v3_pre_topc(X0_51,sK2) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,X0_51),X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_6657])).

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

cnf(c_566,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_567,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | v5_pre_topc(sK4,X0,X1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK0(X0,X1,sK4)),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_2429,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | v5_pre_topc(sK4,X0_52,X1_52)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),u1_struct_0(X1_52),sK4,sK0(X0_52,X1_52,sK4)),X0_52)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(X1_52)
    | k2_struct_0(X1_52) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_567])).

cnf(c_2864,plain,
    ( k2_struct_0(X0_52) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v5_pre_topc(sK4,X1_52,X0_52) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1_52),u1_struct_0(X0_52),sK4,sK0(X1_52,X0_52,sK4)),X1_52) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2429])).

cnf(c_5238,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X0_52),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,sK0(X0_52,sK3,sK4)),X0_52) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3587,c_2864])).

cnf(c_5263,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,sK0(X0_52,sK3,sK4)),X0_52) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5238,c_3587])).

cnf(c_34,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8086,plain,
    ( l1_pre_topc(X0_52) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,sK0(X0_52,sK3,sK4)),X0_52) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5263,c_23,c_34,c_2475,c_2438,c_3154,c_3155,c_3259])).

cnf(c_8087,plain,
    ( v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,sK0(X0_52,sK3,sK4)),X0_52) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_8086])).

cnf(c_8098,plain,
    ( v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK2) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | v3_pre_topc(sK0(X0_52,sK3,sK4),sK2) != iProver_top
    | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_6658,c_8087])).

cnf(c_8145,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top
    | v5_pre_topc(sK4,sK1,sK3) = iProver_top
    | v3_pre_topc(sK0(sK1,sK3,sK4),sK2) != iProver_top
    | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8098])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2442,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2854,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2442])).

cnf(c_3589,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2854,c_2857])).

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

cnf(c_458,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_459,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | v5_pre_topc(sK4,X0,X1)
    | m1_subset_1(sK0(X0,X1,sK4),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_2433,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | v5_pre_topc(sK4,X0_52,X1_52)
    | m1_subset_1(sK0(X0_52,X1_52,sK4),k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(X1_52)
    | k2_struct_0(X1_52) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_459])).

cnf(c_2860,plain,
    ( k2_struct_0(X0_52) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v5_pre_topc(sK4,X1_52,X0_52) = iProver_top
    | m1_subset_1(sK0(X1_52,X0_52,sK4),k1_zfmisc_1(u1_struct_0(X0_52))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2433])).

cnf(c_4972,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X0_52),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3587,c_2860])).

cnf(c_4997,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4972,c_3587])).

cnf(c_6612,plain,
    ( l1_pre_topc(X0_52) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4997,c_23,c_34,c_2475,c_2438,c_3154,c_3155,c_3259])).

cnf(c_6613,plain,
    ( v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_6612])).

cnf(c_6623,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK3) = iProver_top
    | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3589,c_6613])).

cnf(c_6648,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK3) = iProver_top
    | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6623,c_3589])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

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

cnf(c_2441,negated_conjecture,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_154])).

cnf(c_2855,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2441])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2448,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2849,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2448])).

cnf(c_2886,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2849,c_2445])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2446,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2851,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2446])).

cnf(c_2881,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2851,c_2445])).

cnf(c_2918,plain,
    ( v5_pre_topc(sK4,sK1,sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2855,c_2886,c_2881])).

cnf(c_3726,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3587,c_2886])).

cnf(c_3727,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3587,c_2881])).

cnf(c_5067,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK3) = iProver_top
    | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4997])).

cnf(c_6898,plain,
    ( m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6648,c_30,c_23,c_34,c_2475,c_2438,c_2918,c_3154,c_3155,c_3259,c_3726,c_3727,c_5067])).

cnf(c_4,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2450,plain,
    ( v3_pre_topc(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ r2_hidden(X0_51,u1_pre_topc(X0_52))
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2847,plain,
    ( v3_pre_topc(X0_51,X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | r2_hidden(X0_51,u1_pre_topc(X0_52)) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2450])).

cnf(c_3235,plain,
    ( v3_pre_topc(X0_51,sK2) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0_51,u1_pre_topc(sK2)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2445,c_2847])).

cnf(c_3268,plain,
    ( r2_hidden(X0_51,u1_pre_topc(sK2)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(X0_51,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3235,c_32])).

cnf(c_3269,plain,
    ( v3_pre_topc(X0_51,sK2) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0_51,u1_pre_topc(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3268])).

cnf(c_3725,plain,
    ( v3_pre_topc(X0_51,sK2) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0_51,u1_pre_topc(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3587,c_3269])).

cnf(c_6906,plain,
    ( v3_pre_topc(sK0(sK1,sK3,sK4),sK2) = iProver_top
    | r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6898,c_3725])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2451,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ r2_hidden(X2_51,X0_51)
    | r2_hidden(X2_51,X1_51) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_5446,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(X0_51))
    | r2_hidden(sK0(sK1,sK3,sK4),X0_51)
    | ~ r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK3)) ),
    inference(instantiation,[status(thm)],[c_2451])).

cnf(c_6593,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(u1_pre_topc(sK2)))
    | r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK2))
    | ~ r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK3)) ),
    inference(instantiation,[status(thm)],[c_5446])).

cnf(c_6594,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(u1_pre_topc(sK2))) != iProver_top
    | r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK2)) = iProver_top
    | r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6593])).

cnf(c_5,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2449,plain,
    ( ~ v3_pre_topc(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52)))
    | r2_hidden(X0_51,u1_pre_topc(X0_52))
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_4592,plain,
    ( ~ v3_pre_topc(sK0(sK1,sK3,sK4),sK3)
    | ~ m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2449])).

cnf(c_4598,plain,
    ( v3_pre_topc(sK0(sK1,sK3,sK4),sK3) != iProver_top
    | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK3)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4592])).

cnf(c_4147,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK1,sK3)
    | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | k2_struct_0(sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2433])).

cnf(c_4151,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK3) = iProver_top
    | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4147])).

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

cnf(c_512,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v3_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_513,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | v5_pre_topc(sK4,X0,X1)
    | v3_pre_topc(sK0(X0,X1,sK4),X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_2431,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | v5_pre_topc(sK4,X0_52,X1_52)
    | v3_pre_topc(sK0(X0_52,X1_52,sK4),X1_52)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(X1_52)
    | k2_struct_0(X1_52) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_513])).

cnf(c_2862,plain,
    ( k2_struct_0(X0_52) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v5_pre_topc(sK4,X1_52,X0_52) = iProver_top
    | v3_pre_topc(sK0(X1_52,X0_52,sK4),X0_52) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2431])).

cnf(c_3462,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK3) = iProver_top
    | v3_pre_topc(sK0(sK1,sK3,sK4),sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2886,c_2862])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_306,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_pre_topc(sK2) != X1
    | u1_pre_topc(sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_307,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(u1_pre_topc(sK2))) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_308,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_18,negated_conjecture,
    ( v5_pre_topc(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_38,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8145,c_6906,c_6594,c_5067,c_4598,c_4151,c_3727,c_3726,c_3462,c_3259,c_3155,c_3154,c_2881,c_2918,c_2886,c_2438,c_2475,c_308,c_38,c_34,c_23,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:27:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.99/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/0.97  
% 2.99/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.99/0.97  
% 2.99/0.97  ------  iProver source info
% 2.99/0.97  
% 2.99/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.99/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.99/0.97  git: non_committed_changes: false
% 2.99/0.97  git: last_make_outside_of_git: false
% 2.99/0.97  
% 2.99/0.97  ------ 
% 2.99/0.97  
% 2.99/0.97  ------ Input Options
% 2.99/0.97  
% 2.99/0.97  --out_options                           all
% 2.99/0.97  --tptp_safe_out                         true
% 2.99/0.97  --problem_path                          ""
% 2.99/0.97  --include_path                          ""
% 2.99/0.97  --clausifier                            res/vclausify_rel
% 2.99/0.97  --clausifier_options                    --mode clausify
% 2.99/0.97  --stdin                                 false
% 2.99/0.97  --stats_out                             all
% 2.99/0.97  
% 2.99/0.97  ------ General Options
% 2.99/0.97  
% 2.99/0.97  --fof                                   false
% 2.99/0.97  --time_out_real                         305.
% 2.99/0.97  --time_out_virtual                      -1.
% 2.99/0.97  --symbol_type_check                     false
% 2.99/0.97  --clausify_out                          false
% 2.99/0.97  --sig_cnt_out                           false
% 2.99/0.97  --trig_cnt_out                          false
% 2.99/0.97  --trig_cnt_out_tolerance                1.
% 2.99/0.97  --trig_cnt_out_sk_spl                   false
% 2.99/0.97  --abstr_cl_out                          false
% 2.99/0.97  
% 2.99/0.97  ------ Global Options
% 2.99/0.97  
% 2.99/0.97  --schedule                              default
% 2.99/0.97  --add_important_lit                     false
% 2.99/0.97  --prop_solver_per_cl                    1000
% 2.99/0.97  --min_unsat_core                        false
% 2.99/0.97  --soft_assumptions                      false
% 2.99/0.97  --soft_lemma_size                       3
% 2.99/0.97  --prop_impl_unit_size                   0
% 2.99/0.97  --prop_impl_unit                        []
% 2.99/0.97  --share_sel_clauses                     true
% 2.99/0.97  --reset_solvers                         false
% 2.99/0.97  --bc_imp_inh                            [conj_cone]
% 2.99/0.97  --conj_cone_tolerance                   3.
% 2.99/0.97  --extra_neg_conj                        none
% 2.99/0.97  --large_theory_mode                     true
% 2.99/0.97  --prolific_symb_bound                   200
% 2.99/0.97  --lt_threshold                          2000
% 2.99/0.97  --clause_weak_htbl                      true
% 2.99/0.97  --gc_record_bc_elim                     false
% 2.99/0.97  
% 2.99/0.97  ------ Preprocessing Options
% 2.99/0.97  
% 2.99/0.97  --preprocessing_flag                    true
% 2.99/0.97  --time_out_prep_mult                    0.1
% 2.99/0.97  --splitting_mode                        input
% 2.99/0.97  --splitting_grd                         true
% 2.99/0.97  --splitting_cvd                         false
% 2.99/0.97  --splitting_cvd_svl                     false
% 2.99/0.97  --splitting_nvd                         32
% 2.99/0.97  --sub_typing                            true
% 2.99/0.97  --prep_gs_sim                           true
% 2.99/0.97  --prep_unflatten                        true
% 2.99/0.97  --prep_res_sim                          true
% 2.99/0.97  --prep_upred                            true
% 2.99/0.97  --prep_sem_filter                       exhaustive
% 2.99/0.97  --prep_sem_filter_out                   false
% 2.99/0.97  --pred_elim                             true
% 2.99/0.97  --res_sim_input                         true
% 2.99/0.97  --eq_ax_congr_red                       true
% 2.99/0.97  --pure_diseq_elim                       true
% 2.99/0.97  --brand_transform                       false
% 2.99/0.97  --non_eq_to_eq                          false
% 2.99/0.97  --prep_def_merge                        true
% 2.99/0.97  --prep_def_merge_prop_impl              false
% 2.99/0.97  --prep_def_merge_mbd                    true
% 2.99/0.97  --prep_def_merge_tr_red                 false
% 2.99/0.97  --prep_def_merge_tr_cl                  false
% 2.99/0.97  --smt_preprocessing                     true
% 2.99/0.97  --smt_ac_axioms                         fast
% 2.99/0.97  --preprocessed_out                      false
% 2.99/0.97  --preprocessed_stats                    false
% 2.99/0.97  
% 2.99/0.97  ------ Abstraction refinement Options
% 2.99/0.97  
% 2.99/0.97  --abstr_ref                             []
% 2.99/0.97  --abstr_ref_prep                        false
% 2.99/0.97  --abstr_ref_until_sat                   false
% 2.99/0.97  --abstr_ref_sig_restrict                funpre
% 2.99/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.97  --abstr_ref_under                       []
% 2.99/0.97  
% 2.99/0.97  ------ SAT Options
% 2.99/0.97  
% 2.99/0.97  --sat_mode                              false
% 2.99/0.97  --sat_fm_restart_options                ""
% 2.99/0.97  --sat_gr_def                            false
% 2.99/0.97  --sat_epr_types                         true
% 2.99/0.97  --sat_non_cyclic_types                  false
% 2.99/0.97  --sat_finite_models                     false
% 2.99/0.97  --sat_fm_lemmas                         false
% 2.99/0.97  --sat_fm_prep                           false
% 2.99/0.97  --sat_fm_uc_incr                        true
% 2.99/0.97  --sat_out_model                         small
% 2.99/0.97  --sat_out_clauses                       false
% 2.99/0.97  
% 2.99/0.97  ------ QBF Options
% 2.99/0.97  
% 2.99/0.97  --qbf_mode                              false
% 2.99/0.97  --qbf_elim_univ                         false
% 2.99/0.97  --qbf_dom_inst                          none
% 2.99/0.97  --qbf_dom_pre_inst                      false
% 2.99/0.97  --qbf_sk_in                             false
% 2.99/0.97  --qbf_pred_elim                         true
% 2.99/0.97  --qbf_split                             512
% 2.99/0.97  
% 2.99/0.97  ------ BMC1 Options
% 2.99/0.97  
% 2.99/0.97  --bmc1_incremental                      false
% 2.99/0.97  --bmc1_axioms                           reachable_all
% 2.99/0.97  --bmc1_min_bound                        0
% 2.99/0.97  --bmc1_max_bound                        -1
% 2.99/0.97  --bmc1_max_bound_default                -1
% 2.99/0.97  --bmc1_symbol_reachability              true
% 2.99/0.97  --bmc1_property_lemmas                  false
% 2.99/0.97  --bmc1_k_induction                      false
% 2.99/0.97  --bmc1_non_equiv_states                 false
% 2.99/0.97  --bmc1_deadlock                         false
% 2.99/0.97  --bmc1_ucm                              false
% 2.99/0.97  --bmc1_add_unsat_core                   none
% 2.99/0.97  --bmc1_unsat_core_children              false
% 2.99/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.97  --bmc1_out_stat                         full
% 2.99/0.97  --bmc1_ground_init                      false
% 2.99/0.97  --bmc1_pre_inst_next_state              false
% 2.99/0.97  --bmc1_pre_inst_state                   false
% 2.99/0.97  --bmc1_pre_inst_reach_state             false
% 2.99/0.97  --bmc1_out_unsat_core                   false
% 2.99/0.97  --bmc1_aig_witness_out                  false
% 2.99/0.97  --bmc1_verbose                          false
% 2.99/0.97  --bmc1_dump_clauses_tptp                false
% 2.99/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.97  --bmc1_dump_file                        -
% 2.99/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.97  --bmc1_ucm_extend_mode                  1
% 2.99/0.97  --bmc1_ucm_init_mode                    2
% 2.99/0.97  --bmc1_ucm_cone_mode                    none
% 2.99/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.97  --bmc1_ucm_relax_model                  4
% 2.99/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.97  --bmc1_ucm_layered_model                none
% 2.99/0.97  --bmc1_ucm_max_lemma_size               10
% 2.99/0.97  
% 2.99/0.97  ------ AIG Options
% 2.99/0.97  
% 2.99/0.97  --aig_mode                              false
% 2.99/0.97  
% 2.99/0.97  ------ Instantiation Options
% 2.99/0.97  
% 2.99/0.97  --instantiation_flag                    true
% 2.99/0.97  --inst_sos_flag                         false
% 2.99/0.97  --inst_sos_phase                        true
% 2.99/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.97  --inst_lit_sel_side                     num_symb
% 2.99/0.97  --inst_solver_per_active                1400
% 2.99/0.97  --inst_solver_calls_frac                1.
% 2.99/0.97  --inst_passive_queue_type               priority_queues
% 2.99/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.97  --inst_passive_queues_freq              [25;2]
% 2.99/0.97  --inst_dismatching                      true
% 2.99/0.97  --inst_eager_unprocessed_to_passive     true
% 2.99/0.97  --inst_prop_sim_given                   true
% 2.99/0.97  --inst_prop_sim_new                     false
% 2.99/0.97  --inst_subs_new                         false
% 2.99/0.97  --inst_eq_res_simp                      false
% 2.99/0.97  --inst_subs_given                       false
% 2.99/0.97  --inst_orphan_elimination               true
% 2.99/0.97  --inst_learning_loop_flag               true
% 2.99/0.97  --inst_learning_start                   3000
% 2.99/0.97  --inst_learning_factor                  2
% 2.99/0.97  --inst_start_prop_sim_after_learn       3
% 2.99/0.97  --inst_sel_renew                        solver
% 2.99/0.97  --inst_lit_activity_flag                true
% 2.99/0.97  --inst_restr_to_given                   false
% 2.99/0.97  --inst_activity_threshold               500
% 2.99/0.97  --inst_out_proof                        true
% 2.99/0.97  
% 2.99/0.97  ------ Resolution Options
% 2.99/0.97  
% 2.99/0.97  --resolution_flag                       true
% 2.99/0.97  --res_lit_sel                           adaptive
% 2.99/0.97  --res_lit_sel_side                      none
% 2.99/0.97  --res_ordering                          kbo
% 2.99/0.97  --res_to_prop_solver                    active
% 2.99/0.97  --res_prop_simpl_new                    false
% 2.99/0.97  --res_prop_simpl_given                  true
% 2.99/0.97  --res_passive_queue_type                priority_queues
% 2.99/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.97  --res_passive_queues_freq               [15;5]
% 2.99/0.97  --res_forward_subs                      full
% 2.99/0.97  --res_backward_subs                     full
% 2.99/0.97  --res_forward_subs_resolution           true
% 2.99/0.97  --res_backward_subs_resolution          true
% 2.99/0.97  --res_orphan_elimination                true
% 2.99/0.97  --res_time_limit                        2.
% 2.99/0.97  --res_out_proof                         true
% 2.99/0.97  
% 2.99/0.97  ------ Superposition Options
% 2.99/0.97  
% 2.99/0.97  --superposition_flag                    true
% 2.99/0.97  --sup_passive_queue_type                priority_queues
% 2.99/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.97  --demod_completeness_check              fast
% 2.99/0.97  --demod_use_ground                      true
% 2.99/0.97  --sup_to_prop_solver                    passive
% 2.99/0.97  --sup_prop_simpl_new                    true
% 2.99/0.97  --sup_prop_simpl_given                  true
% 2.99/0.97  --sup_fun_splitting                     false
% 2.99/0.97  --sup_smt_interval                      50000
% 2.99/0.97  
% 2.99/0.97  ------ Superposition Simplification Setup
% 2.99/0.97  
% 2.99/0.97  --sup_indices_passive                   []
% 2.99/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.97  --sup_full_bw                           [BwDemod]
% 2.99/0.97  --sup_immed_triv                        [TrivRules]
% 2.99/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.97  --sup_immed_bw_main                     []
% 2.99/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.97  
% 2.99/0.97  ------ Combination Options
% 2.99/0.97  
% 2.99/0.97  --comb_res_mult                         3
% 2.99/0.97  --comb_sup_mult                         2
% 2.99/0.97  --comb_inst_mult                        10
% 2.99/0.97  
% 2.99/0.97  ------ Debug Options
% 2.99/0.97  
% 2.99/0.97  --dbg_backtrace                         false
% 2.99/0.97  --dbg_dump_prop_clauses                 false
% 2.99/0.97  --dbg_dump_prop_clauses_file            -
% 2.99/0.97  --dbg_out_stat                          false
% 2.99/0.97  ------ Parsing...
% 2.99/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.99/0.97  
% 2.99/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.99/0.97  
% 2.99/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.99/0.97  
% 2.99/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.99/0.97  ------ Proving...
% 2.99/0.97  ------ Problem Properties 
% 2.99/0.97  
% 2.99/0.97  
% 2.99/0.97  clauses                                 24
% 2.99/0.97  conjectures                             8
% 2.99/0.97  EPR                                     4
% 2.99/0.97  Horn                                    18
% 2.99/0.97  unary                                   11
% 2.99/0.97  binary                                  1
% 2.99/0.97  lits                                    87
% 2.99/0.97  lits eq                                 13
% 2.99/0.97  fd_pure                                 0
% 2.99/0.97  fd_pseudo                               0
% 2.99/0.97  fd_cond                                 0
% 2.99/0.97  fd_pseudo_cond                          0
% 2.99/0.97  AC symbols                              0
% 2.99/0.97  
% 2.99/0.97  ------ Schedule dynamic 5 is on 
% 2.99/0.97  
% 2.99/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.99/0.97  
% 2.99/0.97  
% 2.99/0.97  ------ 
% 2.99/0.97  Current options:
% 2.99/0.97  ------ 
% 2.99/0.97  
% 2.99/0.97  ------ Input Options
% 2.99/0.97  
% 2.99/0.97  --out_options                           all
% 2.99/0.97  --tptp_safe_out                         true
% 2.99/0.97  --problem_path                          ""
% 2.99/0.97  --include_path                          ""
% 2.99/0.97  --clausifier                            res/vclausify_rel
% 2.99/0.97  --clausifier_options                    --mode clausify
% 2.99/0.97  --stdin                                 false
% 2.99/0.97  --stats_out                             all
% 2.99/0.97  
% 2.99/0.97  ------ General Options
% 2.99/0.97  
% 2.99/0.97  --fof                                   false
% 2.99/0.97  --time_out_real                         305.
% 2.99/0.97  --time_out_virtual                      -1.
% 2.99/0.97  --symbol_type_check                     false
% 2.99/0.97  --clausify_out                          false
% 2.99/0.97  --sig_cnt_out                           false
% 2.99/0.97  --trig_cnt_out                          false
% 2.99/0.97  --trig_cnt_out_tolerance                1.
% 2.99/0.97  --trig_cnt_out_sk_spl                   false
% 2.99/0.97  --abstr_cl_out                          false
% 2.99/0.97  
% 2.99/0.97  ------ Global Options
% 2.99/0.97  
% 2.99/0.97  --schedule                              default
% 2.99/0.97  --add_important_lit                     false
% 2.99/0.97  --prop_solver_per_cl                    1000
% 2.99/0.97  --min_unsat_core                        false
% 2.99/0.97  --soft_assumptions                      false
% 2.99/0.97  --soft_lemma_size                       3
% 2.99/0.97  --prop_impl_unit_size                   0
% 2.99/0.97  --prop_impl_unit                        []
% 2.99/0.97  --share_sel_clauses                     true
% 2.99/0.97  --reset_solvers                         false
% 2.99/0.97  --bc_imp_inh                            [conj_cone]
% 2.99/0.97  --conj_cone_tolerance                   3.
% 2.99/0.97  --extra_neg_conj                        none
% 2.99/0.97  --large_theory_mode                     true
% 2.99/0.97  --prolific_symb_bound                   200
% 2.99/0.97  --lt_threshold                          2000
% 2.99/0.97  --clause_weak_htbl                      true
% 2.99/0.97  --gc_record_bc_elim                     false
% 2.99/0.97  
% 2.99/0.97  ------ Preprocessing Options
% 2.99/0.97  
% 2.99/0.97  --preprocessing_flag                    true
% 2.99/0.97  --time_out_prep_mult                    0.1
% 2.99/0.97  --splitting_mode                        input
% 2.99/0.97  --splitting_grd                         true
% 2.99/0.97  --splitting_cvd                         false
% 2.99/0.97  --splitting_cvd_svl                     false
% 2.99/0.97  --splitting_nvd                         32
% 2.99/0.97  --sub_typing                            true
% 2.99/0.97  --prep_gs_sim                           true
% 2.99/0.97  --prep_unflatten                        true
% 2.99/0.97  --prep_res_sim                          true
% 2.99/0.97  --prep_upred                            true
% 2.99/0.97  --prep_sem_filter                       exhaustive
% 2.99/0.97  --prep_sem_filter_out                   false
% 2.99/0.97  --pred_elim                             true
% 2.99/0.97  --res_sim_input                         true
% 2.99/0.97  --eq_ax_congr_red                       true
% 2.99/0.97  --pure_diseq_elim                       true
% 2.99/0.97  --brand_transform                       false
% 2.99/0.97  --non_eq_to_eq                          false
% 2.99/0.97  --prep_def_merge                        true
% 2.99/0.97  --prep_def_merge_prop_impl              false
% 2.99/0.97  --prep_def_merge_mbd                    true
% 2.99/0.97  --prep_def_merge_tr_red                 false
% 2.99/0.97  --prep_def_merge_tr_cl                  false
% 2.99/0.97  --smt_preprocessing                     true
% 2.99/0.97  --smt_ac_axioms                         fast
% 2.99/0.97  --preprocessed_out                      false
% 2.99/0.97  --preprocessed_stats                    false
% 2.99/0.97  
% 2.99/0.97  ------ Abstraction refinement Options
% 2.99/0.97  
% 2.99/0.97  --abstr_ref                             []
% 2.99/0.97  --abstr_ref_prep                        false
% 2.99/0.97  --abstr_ref_until_sat                   false
% 2.99/0.97  --abstr_ref_sig_restrict                funpre
% 2.99/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.97  --abstr_ref_under                       []
% 2.99/0.97  
% 2.99/0.97  ------ SAT Options
% 2.99/0.97  
% 2.99/0.97  --sat_mode                              false
% 2.99/0.97  --sat_fm_restart_options                ""
% 2.99/0.97  --sat_gr_def                            false
% 2.99/0.97  --sat_epr_types                         true
% 2.99/0.97  --sat_non_cyclic_types                  false
% 2.99/0.97  --sat_finite_models                     false
% 2.99/0.97  --sat_fm_lemmas                         false
% 2.99/0.97  --sat_fm_prep                           false
% 2.99/0.97  --sat_fm_uc_incr                        true
% 2.99/0.97  --sat_out_model                         small
% 2.99/0.97  --sat_out_clauses                       false
% 2.99/0.97  
% 2.99/0.97  ------ QBF Options
% 2.99/0.97  
% 2.99/0.97  --qbf_mode                              false
% 2.99/0.97  --qbf_elim_univ                         false
% 2.99/0.97  --qbf_dom_inst                          none
% 2.99/0.97  --qbf_dom_pre_inst                      false
% 2.99/0.97  --qbf_sk_in                             false
% 2.99/0.97  --qbf_pred_elim                         true
% 2.99/0.97  --qbf_split                             512
% 2.99/0.97  
% 2.99/0.97  ------ BMC1 Options
% 2.99/0.97  
% 2.99/0.97  --bmc1_incremental                      false
% 2.99/0.97  --bmc1_axioms                           reachable_all
% 2.99/0.97  --bmc1_min_bound                        0
% 2.99/0.97  --bmc1_max_bound                        -1
% 2.99/0.97  --bmc1_max_bound_default                -1
% 2.99/0.97  --bmc1_symbol_reachability              true
% 2.99/0.97  --bmc1_property_lemmas                  false
% 2.99/0.97  --bmc1_k_induction                      false
% 2.99/0.97  --bmc1_non_equiv_states                 false
% 2.99/0.97  --bmc1_deadlock                         false
% 2.99/0.97  --bmc1_ucm                              false
% 2.99/0.97  --bmc1_add_unsat_core                   none
% 2.99/0.97  --bmc1_unsat_core_children              false
% 2.99/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.97  --bmc1_out_stat                         full
% 2.99/0.97  --bmc1_ground_init                      false
% 2.99/0.97  --bmc1_pre_inst_next_state              false
% 2.99/0.97  --bmc1_pre_inst_state                   false
% 2.99/0.97  --bmc1_pre_inst_reach_state             false
% 2.99/0.97  --bmc1_out_unsat_core                   false
% 2.99/0.97  --bmc1_aig_witness_out                  false
% 2.99/0.97  --bmc1_verbose                          false
% 2.99/0.97  --bmc1_dump_clauses_tptp                false
% 2.99/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.97  --bmc1_dump_file                        -
% 2.99/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.97  --bmc1_ucm_extend_mode                  1
% 2.99/0.97  --bmc1_ucm_init_mode                    2
% 2.99/0.97  --bmc1_ucm_cone_mode                    none
% 2.99/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.97  --bmc1_ucm_relax_model                  4
% 2.99/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.97  --bmc1_ucm_layered_model                none
% 2.99/0.97  --bmc1_ucm_max_lemma_size               10
% 2.99/0.97  
% 2.99/0.97  ------ AIG Options
% 2.99/0.97  
% 2.99/0.97  --aig_mode                              false
% 2.99/0.97  
% 2.99/0.97  ------ Instantiation Options
% 2.99/0.97  
% 2.99/0.97  --instantiation_flag                    true
% 2.99/0.97  --inst_sos_flag                         false
% 2.99/0.97  --inst_sos_phase                        true
% 2.99/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.97  --inst_lit_sel_side                     none
% 2.99/0.97  --inst_solver_per_active                1400
% 2.99/0.97  --inst_solver_calls_frac                1.
% 2.99/0.97  --inst_passive_queue_type               priority_queues
% 2.99/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.97  --inst_passive_queues_freq              [25;2]
% 2.99/0.97  --inst_dismatching                      true
% 2.99/0.97  --inst_eager_unprocessed_to_passive     true
% 2.99/0.97  --inst_prop_sim_given                   true
% 2.99/0.97  --inst_prop_sim_new                     false
% 2.99/0.97  --inst_subs_new                         false
% 2.99/0.97  --inst_eq_res_simp                      false
% 2.99/0.97  --inst_subs_given                       false
% 2.99/0.97  --inst_orphan_elimination               true
% 2.99/0.97  --inst_learning_loop_flag               true
% 2.99/0.97  --inst_learning_start                   3000
% 2.99/0.97  --inst_learning_factor                  2
% 2.99/0.97  --inst_start_prop_sim_after_learn       3
% 2.99/0.97  --inst_sel_renew                        solver
% 2.99/0.97  --inst_lit_activity_flag                true
% 2.99/0.97  --inst_restr_to_given                   false
% 2.99/0.97  --inst_activity_threshold               500
% 2.99/0.97  --inst_out_proof                        true
% 2.99/0.97  
% 2.99/0.97  ------ Resolution Options
% 2.99/0.97  
% 2.99/0.97  --resolution_flag                       false
% 2.99/0.97  --res_lit_sel                           adaptive
% 2.99/0.97  --res_lit_sel_side                      none
% 2.99/0.97  --res_ordering                          kbo
% 2.99/0.97  --res_to_prop_solver                    active
% 2.99/0.97  --res_prop_simpl_new                    false
% 2.99/0.97  --res_prop_simpl_given                  true
% 2.99/0.97  --res_passive_queue_type                priority_queues
% 2.99/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.97  --res_passive_queues_freq               [15;5]
% 2.99/0.97  --res_forward_subs                      full
% 2.99/0.97  --res_backward_subs                     full
% 2.99/0.97  --res_forward_subs_resolution           true
% 2.99/0.97  --res_backward_subs_resolution          true
% 2.99/0.97  --res_orphan_elimination                true
% 2.99/0.97  --res_time_limit                        2.
% 2.99/0.97  --res_out_proof                         true
% 2.99/0.97  
% 2.99/0.97  ------ Superposition Options
% 2.99/0.97  
% 2.99/0.97  --superposition_flag                    true
% 2.99/0.97  --sup_passive_queue_type                priority_queues
% 2.99/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.97  --demod_completeness_check              fast
% 2.99/0.97  --demod_use_ground                      true
% 2.99/0.97  --sup_to_prop_solver                    passive
% 2.99/0.97  --sup_prop_simpl_new                    true
% 2.99/0.97  --sup_prop_simpl_given                  true
% 2.99/0.97  --sup_fun_splitting                     false
% 2.99/0.97  --sup_smt_interval                      50000
% 2.99/0.97  
% 2.99/0.97  ------ Superposition Simplification Setup
% 2.99/0.97  
% 2.99/0.97  --sup_indices_passive                   []
% 2.99/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.97  --sup_full_bw                           [BwDemod]
% 2.99/0.97  --sup_immed_triv                        [TrivRules]
% 2.99/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.97  --sup_immed_bw_main                     []
% 2.99/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.97  
% 2.99/0.97  ------ Combination Options
% 2.99/0.97  
% 2.99/0.97  --comb_res_mult                         3
% 2.99/0.97  --comb_sup_mult                         2
% 2.99/0.97  --comb_inst_mult                        10
% 2.99/0.97  
% 2.99/0.97  ------ Debug Options
% 2.99/0.97  
% 2.99/0.97  --dbg_backtrace                         false
% 2.99/0.97  --dbg_dump_prop_clauses                 false
% 2.99/0.97  --dbg_dump_prop_clauses_file            -
% 2.99/0.97  --dbg_out_stat                          false
% 2.99/0.97  
% 2.99/0.97  
% 2.99/0.97  
% 2.99/0.97  
% 2.99/0.97  ------ Proving...
% 2.99/0.97  
% 2.99/0.97  
% 2.99/0.97  % SZS status Theorem for theBenchmark.p
% 2.99/0.97  
% 2.99/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.99/0.97  
% 2.99/0.97  fof(f9,conjecture,(
% 2.99/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 2.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.97  
% 2.99/0.97  fof(f10,negated_conjecture,(
% 2.99/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 2.99/0.97    inference(negated_conjecture,[],[f9])).
% 2.99/0.97  
% 2.99/0.97  fof(f12,plain,(
% 2.99/0.97    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 2.99/0.97    inference(pure_predicate_removal,[],[f10])).
% 2.99/0.97  
% 2.99/0.97  fof(f22,plain,(
% 2.99/0.97    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3))) & (r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2))) & (l1_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.99/0.97    inference(ennf_transformation,[],[f12])).
% 2.99/0.97  
% 2.99/0.97  fof(f23,plain,(
% 2.99/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.99/0.97    inference(flattening,[],[f22])).
% 2.99/0.97  
% 2.99/0.97  fof(f32,plain,(
% 2.99/0.97    ( ! [X2,X0,X1] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(sK4,X0,X2) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.99/0.97    introduced(choice_axiom,[])).
% 2.99/0.97  
% 2.99/0.97  fof(f31,plain,(
% 2.99/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2) & l1_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(X3,X0,sK3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(sK3),u1_pre_topc(X1)) & u1_struct_0(sK3) = u1_struct_0(X1) & l1_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 2.99/0.97    introduced(choice_axiom,[])).
% 2.99/0.97  
% 2.99/0.97  fof(f30,plain,(
% 2.99/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v5_pre_topc(X3,X0,sK2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(sK2)) & u1_struct_0(sK2) = u1_struct_0(X2) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.99/0.97    introduced(choice_axiom,[])).
% 2.99/0.97  
% 2.99/0.97  fof(f29,plain,(
% 2.99/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X3,X0,X1) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK1,X2) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v5_pre_topc(X3,sK1,X1) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) & u1_struct_0(X1) = u1_struct_0(X2) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.99/0.97    introduced(choice_axiom,[])).
% 2.99/0.97  
% 2.99/0.97  fof(f33,plain,(
% 2.99/0.97    ((((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(sK4,sK1,sK2) & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK4)) & r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2)) & u1_struct_0(sK2) = u1_struct_0(sK3) & l1_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.99/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f32,f31,f30,f29])).
% 2.99/0.97  
% 2.99/0.97  fof(f55,plain,(
% 2.99/0.97    l1_pre_topc(sK3)),
% 2.99/0.97    inference(cnf_transformation,[],[f33])).
% 2.99/0.97  
% 2.99/0.97  fof(f6,axiom,(
% 2.99/0.97    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.97  
% 2.99/0.97  fof(f17,plain,(
% 2.99/0.97    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.99/0.97    inference(ennf_transformation,[],[f6])).
% 2.99/0.97  
% 2.99/0.97  fof(f40,plain,(
% 2.99/0.97    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.99/0.97    inference(cnf_transformation,[],[f17])).
% 2.99/0.97  
% 2.99/0.97  fof(f4,axiom,(
% 2.99/0.97    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.97  
% 2.99/0.97  fof(f15,plain,(
% 2.99/0.97    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.99/0.97    inference(ennf_transformation,[],[f4])).
% 2.99/0.97  
% 2.99/0.97  fof(f37,plain,(
% 2.99/0.97    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.99/0.97    inference(cnf_transformation,[],[f15])).
% 2.99/0.97  
% 2.99/0.97  fof(f56,plain,(
% 2.99/0.97    u1_struct_0(sK2) = u1_struct_0(sK3)),
% 2.99/0.97    inference(cnf_transformation,[],[f33])).
% 2.99/0.97  
% 2.99/0.97  fof(f8,axiom,(
% 2.99/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 2.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.97  
% 2.99/0.97  fof(f20,plain,(
% 2.99/0.97    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.99/0.97    inference(ennf_transformation,[],[f8])).
% 2.99/0.97  
% 2.99/0.97  fof(f21,plain,(
% 2.99/0.97    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.99/0.97    inference(flattening,[],[f20])).
% 2.99/0.97  
% 2.99/0.97  fof(f25,plain,(
% 2.99/0.97    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.99/0.97    inference(nnf_transformation,[],[f21])).
% 2.99/0.97  
% 2.99/0.97  fof(f26,plain,(
% 2.99/0.97    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.99/0.97    inference(rectify,[],[f25])).
% 2.99/0.97  
% 2.99/0.97  fof(f27,plain,(
% 2.99/0.97    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v3_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.99/0.97    introduced(choice_axiom,[])).
% 2.99/0.97  
% 2.99/0.97  fof(f28,plain,(
% 2.99/0.97    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v3_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.99/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 2.99/0.97  
% 2.99/0.97  fof(f42,plain,(
% 2.99/0.97    ( ! [X4,X2,X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.99/0.97    inference(cnf_transformation,[],[f28])).
% 2.99/0.97  
% 2.99/0.97  fof(f58,plain,(
% 2.99/0.97    v1_funct_1(sK4)),
% 2.99/0.97    inference(cnf_transformation,[],[f33])).
% 2.99/0.97  
% 2.99/0.97  fof(f53,plain,(
% 2.99/0.97    l1_pre_topc(sK2)),
% 2.99/0.97    inference(cnf_transformation,[],[f33])).
% 2.99/0.97  
% 2.99/0.97  fof(f1,axiom,(
% 2.99/0.97    v1_xboole_0(k1_xboole_0)),
% 2.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.97  
% 2.99/0.97  fof(f34,plain,(
% 2.99/0.97    v1_xboole_0(k1_xboole_0)),
% 2.99/0.97    inference(cnf_transformation,[],[f1])).
% 2.99/0.97  
% 2.99/0.97  fof(f7,axiom,(
% 2.99/0.97    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.97  
% 2.99/0.97  fof(f18,plain,(
% 2.99/0.97    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.99/0.97    inference(ennf_transformation,[],[f7])).
% 2.99/0.97  
% 2.99/0.97  fof(f19,plain,(
% 2.99/0.97    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.99/0.97    inference(flattening,[],[f18])).
% 2.99/0.97  
% 2.99/0.97  fof(f41,plain,(
% 2.99/0.97    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.99/0.97    inference(cnf_transformation,[],[f19])).
% 2.99/0.97  
% 2.99/0.97  fof(f54,plain,(
% 2.99/0.97    ~v2_struct_0(sK3)),
% 2.99/0.97    inference(cnf_transformation,[],[f33])).
% 2.99/0.97  
% 2.99/0.97  fof(f48,plain,(
% 2.99/0.97    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.99/0.97    inference(cnf_transformation,[],[f28])).
% 2.99/0.97  
% 2.99/0.97  fof(f51,plain,(
% 2.99/0.97    l1_pre_topc(sK1)),
% 2.99/0.97    inference(cnf_transformation,[],[f33])).
% 2.99/0.97  
% 2.99/0.97  fof(f44,plain,(
% 2.99/0.97    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.99/0.97    inference(cnf_transformation,[],[f28])).
% 2.99/0.97  
% 2.99/0.97  fof(f62,plain,(
% 2.99/0.97    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 2.99/0.97    inference(cnf_transformation,[],[f33])).
% 2.99/0.97  
% 2.99/0.97  fof(f61,plain,(
% 2.99/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 2.99/0.97    inference(cnf_transformation,[],[f33])).
% 2.99/0.97  
% 2.99/0.97  fof(f59,plain,(
% 2.99/0.97    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))),
% 2.99/0.97    inference(cnf_transformation,[],[f33])).
% 2.99/0.97  
% 2.99/0.97  fof(f5,axiom,(
% 2.99/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.97  
% 2.99/0.97  fof(f16,plain,(
% 2.99/0.97    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.99/0.97    inference(ennf_transformation,[],[f5])).
% 2.99/0.97  
% 2.99/0.97  fof(f24,plain,(
% 2.99/0.97    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.99/0.97    inference(nnf_transformation,[],[f16])).
% 2.99/0.97  
% 2.99/0.97  fof(f39,plain,(
% 2.99/0.97    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.99/0.97    inference(cnf_transformation,[],[f24])).
% 2.99/0.97  
% 2.99/0.97  fof(f2,axiom,(
% 2.99/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.97  
% 2.99/0.97  fof(f13,plain,(
% 2.99/0.97    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.99/0.97    inference(ennf_transformation,[],[f2])).
% 2.99/0.97  
% 2.99/0.97  fof(f35,plain,(
% 2.99/0.97    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.99/0.97    inference(cnf_transformation,[],[f13])).
% 2.99/0.97  
% 2.99/0.97  fof(f38,plain,(
% 2.99/0.97    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.99/0.97    inference(cnf_transformation,[],[f24])).
% 2.99/0.97  
% 2.99/0.97  fof(f46,plain,(
% 2.99/0.97    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v3_pre_topc(sK0(X0,X1,X2),X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.99/0.97    inference(cnf_transformation,[],[f28])).
% 2.99/0.97  
% 2.99/0.97  fof(f3,axiom,(
% 2.99/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.99/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.97  
% 2.99/0.97  fof(f11,plain,(
% 2.99/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.99/0.97    inference(unused_predicate_definition_removal,[],[f3])).
% 2.99/0.97  
% 2.99/0.97  fof(f14,plain,(
% 2.99/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 2.99/0.97    inference(ennf_transformation,[],[f11])).
% 2.99/0.97  
% 2.99/0.97  fof(f36,plain,(
% 2.99/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.99/0.97    inference(cnf_transformation,[],[f14])).
% 2.99/0.97  
% 2.99/0.97  fof(f57,plain,(
% 2.99/0.97    r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2))),
% 2.99/0.97    inference(cnf_transformation,[],[f33])).
% 2.99/0.97  
% 2.99/0.97  fof(f60,plain,(
% 2.99/0.97    v5_pre_topc(sK4,sK1,sK2)),
% 2.99/0.97    inference(cnf_transformation,[],[f33])).
% 2.99/0.97  
% 2.99/0.97  cnf(c_23,negated_conjecture,
% 2.99/0.97      ( l1_pre_topc(sK3) ),
% 2.99/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_2444,negated_conjecture,
% 2.99/0.97      ( l1_pre_topc(sK3) ),
% 2.99/0.97      inference(subtyping,[status(esa)],[c_23]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_2852,plain,
% 2.99/0.97      ( l1_pre_topc(sK3) = iProver_top ),
% 2.99/0.97      inference(predicate_to_equality,[status(thm)],[c_2444]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_6,plain,
% 2.99/0.97      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.99/0.97      inference(cnf_transformation,[],[f40]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_3,plain,
% 2.99/0.97      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.99/0.97      inference(cnf_transformation,[],[f37]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_347,plain,
% 2.99/0.97      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.99/0.97      inference(resolution,[status(thm)],[c_6,c_3]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_2439,plain,
% 2.99/0.97      ( ~ l1_pre_topc(X0_52) | u1_struct_0(X0_52) = k2_struct_0(X0_52) ),
% 2.99/0.97      inference(subtyping,[status(esa)],[c_347]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_2857,plain,
% 2.99/0.97      ( u1_struct_0(X0_52) = k2_struct_0(X0_52)
% 2.99/0.97      | l1_pre_topc(X0_52) != iProver_top ),
% 2.99/0.97      inference(predicate_to_equality,[status(thm)],[c_2439]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_3587,plain,
% 2.99/0.97      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.99/0.97      inference(superposition,[status(thm)],[c_2852,c_2857]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_22,negated_conjecture,
% 2.99/0.97      ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
% 2.99/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_2445,negated_conjecture,
% 2.99/0.97      ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
% 2.99/0.97      inference(subtyping,[status(esa)],[c_22]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_3729,plain,
% 2.99/0.97      ( u1_struct_0(sK2) = k2_struct_0(sK3) ),
% 2.99/0.97      inference(demodulation,[status(thm)],[c_3587,c_2445]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_15,plain,
% 2.99/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.97      | ~ v5_pre_topc(X0,X1,X2)
% 2.99/0.97      | ~ v3_pre_topc(X3,X2)
% 2.99/0.97      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 2.99/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.99/0.97      | ~ v1_funct_1(X0)
% 2.99/0.97      | ~ l1_pre_topc(X1)
% 2.99/0.97      | ~ l1_pre_topc(X2)
% 2.99/0.97      | k2_struct_0(X2) = k1_xboole_0 ),
% 2.99/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_20,negated_conjecture,
% 2.99/0.97      ( v1_funct_1(sK4) ),
% 2.99/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_392,plain,
% 2.99/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.97      | ~ v5_pre_topc(X0,X1,X2)
% 2.99/0.97      | ~ v3_pre_topc(X3,X2)
% 2.99/0.97      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 2.99/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.99/0.97      | ~ l1_pre_topc(X1)
% 2.99/0.97      | ~ l1_pre_topc(X2)
% 2.99/0.97      | k2_struct_0(X2) = k1_xboole_0
% 2.99/0.97      | sK4 != X0 ),
% 2.99/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_393,plain,
% 2.99/0.97      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 2.99/0.97      | ~ v5_pre_topc(sK4,X0,X1)
% 2.99/0.97      | ~ v3_pre_topc(X2,X1)
% 2.99/0.97      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2),X0)
% 2.99/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.99/0.97      | ~ l1_pre_topc(X0)
% 2.99/0.97      | ~ l1_pre_topc(X1)
% 2.99/0.97      | k2_struct_0(X1) = k1_xboole_0 ),
% 2.99/0.97      inference(unflattening,[status(thm)],[c_392]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_2435,plain,
% 2.99/0.97      ( ~ v1_funct_2(sK4,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 2.99/0.97      | ~ v5_pre_topc(sK4,X0_52,X1_52)
% 2.99/0.97      | ~ v3_pre_topc(X0_51,X1_52)
% 2.99/0.97      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),u1_struct_0(X1_52),sK4,X0_51),X0_52)
% 2.99/0.97      | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X1_52)))
% 2.99/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 2.99/0.97      | ~ l1_pre_topc(X0_52)
% 2.99/0.97      | ~ l1_pre_topc(X1_52)
% 2.99/0.97      | k2_struct_0(X1_52) = k1_xboole_0 ),
% 2.99/0.97      inference(subtyping,[status(esa)],[c_393]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_2858,plain,
% 2.99/0.97      ( k2_struct_0(X0_52) = k1_xboole_0
% 2.99/0.97      | v1_funct_2(sK4,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 2.99/0.97      | v5_pre_topc(sK4,X1_52,X0_52) != iProver_top
% 2.99/0.97      | v3_pre_topc(X0_51,X0_52) != iProver_top
% 2.99/0.97      | v3_pre_topc(k8_relset_1(u1_struct_0(X1_52),u1_struct_0(X0_52),sK4,X0_51),X1_52) = iProver_top
% 2.99/0.97      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 2.99/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 2.99/0.97      | l1_pre_topc(X1_52) != iProver_top
% 2.99/0.97      | l1_pre_topc(X0_52) != iProver_top ),
% 2.99/0.97      inference(predicate_to_equality,[status(thm)],[c_2435]) ).
% 2.99/0.97  
% 2.99/0.97  cnf(c_4306,plain,
% 2.99/0.97      ( k2_struct_0(sK2) = k1_xboole_0
% 2.99/0.97      | v1_funct_2(sK4,u1_struct_0(X0_52),u1_struct_0(sK2)) != iProver_top
% 2.99/0.97      | v5_pre_topc(sK4,X0_52,sK2) != iProver_top
% 2.99/0.97      | v3_pre_topc(X0_51,sK2) != iProver_top
% 2.99/0.97      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,X0_51),X0_52) = iProver_top
% 2.99/0.97      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.99/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_3729,c_2858]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4316,plain,
% 2.99/0.98      ( k2_struct_0(sK2) = k1_xboole_0
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,sK2) != iProver_top
% 2.99/0.98      | v3_pre_topc(X0_51,sK2) != iProver_top
% 2.99/0.98      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,X0_51),X0_52) = iProver_top
% 2.99/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.99/0.98      inference(light_normalisation,[status(thm)],[c_4306,c_3729]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_25,negated_conjecture,
% 2.99/0.98      ( l1_pre_topc(sK2) ),
% 2.99/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2443,negated_conjecture,
% 2.99/0.98      ( l1_pre_topc(sK2) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_25]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2853,plain,
% 2.99/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2443]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3588,plain,
% 2.99/0.98      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_2853,c_2857]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3930,plain,
% 2.99/0.98      ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
% 2.99/0.98      inference(light_normalisation,[status(thm)],[c_3588,c_3729]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4317,plain,
% 2.99/0.98      ( k2_struct_0(sK3) = k1_xboole_0
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,sK2) != iProver_top
% 2.99/0.98      | v3_pre_topc(X0_51,sK2) != iProver_top
% 2.99/0.98      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,X0_51),X0_52) = iProver_top
% 2.99/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.99/0.98      inference(demodulation,[status(thm)],[c_4316,c_3930]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_32,plain,
% 2.99/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2453,plain,( X0_51 = X0_51 ),theory(equality) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2475,plain,
% 2.99/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_2453]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_0,plain,
% 2.99/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_7,plain,
% 2.99/0.98      ( v2_struct_0(X0)
% 2.99/0.98      | ~ l1_struct_0(X0)
% 2.99/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.99/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_315,plain,
% 2.99/0.98      ( v2_struct_0(X0)
% 2.99/0.98      | ~ l1_struct_0(X0)
% 2.99/0.98      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.99/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_333,plain,
% 2.99/0.98      ( v2_struct_0(X0)
% 2.99/0.98      | ~ l1_pre_topc(X0)
% 2.99/0.98      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.99/0.98      inference(resolution,[status(thm)],[c_6,c_315]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_24,negated_conjecture,
% 2.99/0.98      ( ~ v2_struct_0(sK3) ),
% 2.99/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_365,plain,
% 2.99/0.98      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) != k1_xboole_0 | sK3 != X0 ),
% 2.99/0.98      inference(resolution_lifted,[status(thm)],[c_333,c_24]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_366,plain,
% 2.99/0.98      ( ~ l1_pre_topc(sK3) | u1_struct_0(sK3) != k1_xboole_0 ),
% 2.99/0.98      inference(unflattening,[status(thm)],[c_365]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_368,plain,
% 2.99/0.98      ( u1_struct_0(sK3) != k1_xboole_0 ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_366,c_23]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2438,plain,
% 2.99/0.98      ( u1_struct_0(sK3) != k1_xboole_0 ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_368]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2455,plain,
% 2.99/0.98      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 2.99/0.98      theory(equality) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3098,plain,
% 2.99/0.98      ( u1_struct_0(sK3) != X0_51
% 2.99/0.98      | u1_struct_0(sK3) = k1_xboole_0
% 2.99/0.98      | k1_xboole_0 != X0_51 ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_2455]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3154,plain,
% 2.99/0.98      ( u1_struct_0(sK3) != k2_struct_0(sK3)
% 2.99/0.98      | u1_struct_0(sK3) = k1_xboole_0
% 2.99/0.98      | k1_xboole_0 != k2_struct_0(sK3) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_3098]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3155,plain,
% 2.99/0.98      ( ~ l1_pre_topc(sK3) | u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_2439]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3258,plain,
% 2.99/0.98      ( k2_struct_0(sK3) != X0_51
% 2.99/0.98      | k1_xboole_0 != X0_51
% 2.99/0.98      | k1_xboole_0 = k2_struct_0(sK3) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_2455]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3259,plain,
% 2.99/0.98      ( k2_struct_0(sK3) != k1_xboole_0
% 2.99/0.98      | k1_xboole_0 = k2_struct_0(sK3)
% 2.99/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_3258]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_6657,plain,
% 2.99/0.98      ( l1_pre_topc(X0_52) != iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.99/0.98      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,X0_51),X0_52) = iProver_top
% 2.99/0.98      | v3_pre_topc(X0_51,sK2) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,sK2) != iProver_top
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_4317,c_32,c_23,c_2475,c_2438,c_3154,c_3155,c_3259]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_6658,plain,
% 2.99/0.98      ( v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,sK2) != iProver_top
% 2.99/0.98      | v3_pre_topc(X0_51,sK2) != iProver_top
% 2.99/0.98      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,X0_51),X0_52) = iProver_top
% 2.99/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top ),
% 2.99/0.98      inference(renaming,[status(thm)],[c_6657]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_9,plain,
% 2.99/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.98      | v5_pre_topc(X0,X1,X2)
% 2.99/0.98      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 2.99/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.98      | ~ v1_funct_1(X0)
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | ~ l1_pre_topc(X2)
% 2.99/0.98      | k2_struct_0(X2) = k1_xboole_0 ),
% 2.99/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_566,plain,
% 2.99/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.98      | v5_pre_topc(X0,X1,X2)
% 2.99/0.98      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 2.99/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | ~ l1_pre_topc(X2)
% 2.99/0.98      | k2_struct_0(X2) = k1_xboole_0
% 2.99/0.98      | sK4 != X0 ),
% 2.99/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_567,plain,
% 2.99/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 2.99/0.98      | v5_pre_topc(sK4,X0,X1)
% 2.99/0.98      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK0(X0,X1,sK4)),X0)
% 2.99/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.99/0.98      | ~ l1_pre_topc(X0)
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | k2_struct_0(X1) = k1_xboole_0 ),
% 2.99/0.98      inference(unflattening,[status(thm)],[c_566]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2429,plain,
% 2.99/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,X1_52)
% 2.99/0.98      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),u1_struct_0(X1_52),sK4,sK0(X0_52,X1_52,sK4)),X0_52)
% 2.99/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 2.99/0.98      | ~ l1_pre_topc(X0_52)
% 2.99/0.98      | ~ l1_pre_topc(X1_52)
% 2.99/0.98      | k2_struct_0(X1_52) = k1_xboole_0 ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_567]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2864,plain,
% 2.99/0.98      ( k2_struct_0(X0_52) = k1_xboole_0
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X1_52,X0_52) = iProver_top
% 2.99/0.98      | v3_pre_topc(k8_relset_1(u1_struct_0(X1_52),u1_struct_0(X0_52),sK4,sK0(X1_52,X0_52,sK4)),X1_52) != iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X1_52) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2429]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_5238,plain,
% 2.99/0.98      ( k2_struct_0(sK3) = k1_xboole_0
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(X0_52),u1_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
% 2.99/0.98      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,sK0(X0_52,sK3,sK4)),X0_52) != iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK3) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_3587,c_2864]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_5263,plain,
% 2.99/0.98      ( k2_struct_0(sK3) = k1_xboole_0
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
% 2.99/0.98      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,sK0(X0_52,sK3,sK4)),X0_52) != iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK3) != iProver_top ),
% 2.99/0.98      inference(light_normalisation,[status(thm)],[c_5238,c_3587]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_34,plain,
% 2.99/0.98      ( l1_pre_topc(sK3) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_8086,plain,
% 2.99/0.98      ( l1_pre_topc(X0_52) != iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,sK0(X0_52,sK3,sK4)),X0_52) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_5263,c_23,c_34,c_2475,c_2438,c_3154,c_3155,c_3259]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_8087,plain,
% 2.99/0.98      ( v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
% 2.99/0.98      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_52),k2_struct_0(sK3),sK4,sK0(X0_52,sK3,sK4)),X0_52) != iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top ),
% 2.99/0.98      inference(renaming,[status(thm)],[c_8086]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_8098,plain,
% 2.99/0.98      ( v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,sK2) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
% 2.99/0.98      | v3_pre_topc(sK0(X0_52,sK3,sK4),sK2) != iProver_top
% 2.99/0.98      | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_6658,c_8087]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_8145,plain,
% 2.99/0.98      ( v1_funct_2(sK4,u1_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,sK1,sK2) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,sK1,sK3) = iProver_top
% 2.99/0.98      | v3_pre_topc(sK0(sK1,sK3,sK4),sK2) != iProver_top
% 2.99/0.98      | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_8098]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_27,negated_conjecture,
% 2.99/0.98      ( l1_pre_topc(sK1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2442,negated_conjecture,
% 2.99/0.98      ( l1_pre_topc(sK1) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_27]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2854,plain,
% 2.99/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2442]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3589,plain,
% 2.99/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_2854,c_2857]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_13,plain,
% 2.99/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.98      | v5_pre_topc(X0,X1,X2)
% 2.99/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.98      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 2.99/0.98      | ~ v1_funct_1(X0)
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | ~ l1_pre_topc(X2)
% 2.99/0.98      | k2_struct_0(X2) = k1_xboole_0 ),
% 2.99/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_458,plain,
% 2.99/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.98      | v5_pre_topc(X0,X1,X2)
% 2.99/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.98      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | ~ l1_pre_topc(X2)
% 2.99/0.98      | k2_struct_0(X2) = k1_xboole_0
% 2.99/0.98      | sK4 != X0 ),
% 2.99/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_459,plain,
% 2.99/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 2.99/0.98      | v5_pre_topc(sK4,X0,X1)
% 2.99/0.98      | m1_subset_1(sK0(X0,X1,sK4),k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.99/0.98      | ~ l1_pre_topc(X0)
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | k2_struct_0(X1) = k1_xboole_0 ),
% 2.99/0.98      inference(unflattening,[status(thm)],[c_458]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2433,plain,
% 2.99/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,X1_52)
% 2.99/0.98      | m1_subset_1(sK0(X0_52,X1_52,sK4),k1_zfmisc_1(u1_struct_0(X1_52)))
% 2.99/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 2.99/0.98      | ~ l1_pre_topc(X0_52)
% 2.99/0.98      | ~ l1_pre_topc(X1_52)
% 2.99/0.98      | k2_struct_0(X1_52) = k1_xboole_0 ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_459]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2860,plain,
% 2.99/0.98      ( k2_struct_0(X0_52) = k1_xboole_0
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X1_52,X0_52) = iProver_top
% 2.99/0.98      | m1_subset_1(sK0(X1_52,X0_52,sK4),k1_zfmisc_1(u1_struct_0(X0_52))) = iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X1_52) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2433]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4972,plain,
% 2.99/0.98      ( k2_struct_0(sK3) = k1_xboole_0
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(X0_52),u1_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
% 2.99/0.98      | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK3) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_3587,c_2860]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4997,plain,
% 2.99/0.98      ( k2_struct_0(sK3) = k1_xboole_0
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
% 2.99/0.98      | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK3) != iProver_top ),
% 2.99/0.98      inference(light_normalisation,[status(thm)],[c_4972,c_3587]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_6612,plain,
% 2.99/0.98      ( l1_pre_topc(X0_52) != iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_4997,c_23,c_34,c_2475,c_2438,c_3154,c_3155,c_3259]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_6613,plain,
% 2.99/0.98      ( v1_funct_2(sK4,u1_struct_0(X0_52),k2_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
% 2.99/0.98      | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top ),
% 2.99/0.98      inference(renaming,[status(thm)],[c_6612]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_6623,plain,
% 2.99/0.98      ( v1_funct_2(sK4,u1_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,sK1,sK3) = iProver_top
% 2.99/0.98      | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_3589,c_6613]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_6648,plain,
% 2.99/0.98      ( v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,sK1,sK3) = iProver_top
% 2.99/0.98      | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(light_normalisation,[status(thm)],[c_6623,c_3589]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_30,plain,
% 2.99/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_16,negated_conjecture,
% 2.99/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
% 2.99/0.98      | ~ v5_pre_topc(sK4,sK1,sK3)
% 2.99/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
% 2.99/0.98      | ~ v1_funct_1(sK4) ),
% 2.99/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_153,plain,
% 2.99/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
% 2.99/0.98      | ~ v5_pre_topc(sK4,sK1,sK3)
% 2.99/0.98      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_16,c_20]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_154,negated_conjecture,
% 2.99/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
% 2.99/0.98      | ~ v5_pre_topc(sK4,sK1,sK3)
% 2.99/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) ),
% 2.99/0.98      inference(renaming,[status(thm)],[c_153]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2441,negated_conjecture,
% 2.99/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
% 2.99/0.98      | ~ v5_pre_topc(sK4,sK1,sK3)
% 2.99/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_154]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2855,plain,
% 2.99/0.98      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,sK1,sK3) != iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2441]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_17,negated_conjecture,
% 2.99/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.99/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2448,negated_conjecture,
% 2.99/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2849,plain,
% 2.99/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2448]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2886,plain,
% 2.99/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) = iProver_top ),
% 2.99/0.98      inference(light_normalisation,[status(thm)],[c_2849,c_2445]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_19,negated_conjecture,
% 2.99/0.98      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.99/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2446,negated_conjecture,
% 2.99/0.98      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2851,plain,
% 2.99/0.98      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2446]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2881,plain,
% 2.99/0.98      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) = iProver_top ),
% 2.99/0.98      inference(light_normalisation,[status(thm)],[c_2851,c_2445]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2918,plain,
% 2.99/0.98      ( v5_pre_topc(sK4,sK1,sK3) != iProver_top ),
% 2.99/0.98      inference(forward_subsumption_resolution,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_2855,c_2886,c_2881]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3726,plain,
% 2.99/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK3)))) = iProver_top ),
% 2.99/0.98      inference(demodulation,[status(thm)],[c_3587,c_2886]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3727,plain,
% 2.99/0.98      ( v1_funct_2(sK4,u1_struct_0(sK1),k2_struct_0(sK3)) = iProver_top ),
% 2.99/0.98      inference(demodulation,[status(thm)],[c_3587,c_2881]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_5067,plain,
% 2.99/0.98      ( k2_struct_0(sK3) = k1_xboole_0
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(sK1),k2_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,sK1,sK3) = iProver_top
% 2.99/0.98      | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK3) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_4997]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_6898,plain,
% 2.99/0.98      ( m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_6648,c_30,c_23,c_34,c_2475,c_2438,c_2918,c_3154,
% 2.99/0.98                 c_3155,c_3259,c_3726,c_3727,c_5067]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4,plain,
% 2.99/0.98      ( v3_pre_topc(X0,X1)
% 2.99/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/0.98      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.99/0.98      | ~ l1_pre_topc(X1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2450,plain,
% 2.99/0.98      ( v3_pre_topc(X0_51,X0_52)
% 2.99/0.98      | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52)))
% 2.99/0.98      | ~ r2_hidden(X0_51,u1_pre_topc(X0_52))
% 2.99/0.98      | ~ l1_pre_topc(X0_52) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2847,plain,
% 2.99/0.98      ( v3_pre_topc(X0_51,X0_52) = iProver_top
% 2.99/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 2.99/0.98      | r2_hidden(X0_51,u1_pre_topc(X0_52)) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2450]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3235,plain,
% 2.99/0.98      ( v3_pre_topc(X0_51,sK2) = iProver_top
% 2.99/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/0.98      | r2_hidden(X0_51,u1_pre_topc(sK2)) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_2445,c_2847]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3268,plain,
% 2.99/0.98      ( r2_hidden(X0_51,u1_pre_topc(sK2)) != iProver_top
% 2.99/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/0.98      | v3_pre_topc(X0_51,sK2) = iProver_top ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_3235,c_32]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3269,plain,
% 2.99/0.98      ( v3_pre_topc(X0_51,sK2) = iProver_top
% 2.99/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/0.98      | r2_hidden(X0_51,u1_pre_topc(sK2)) != iProver_top ),
% 2.99/0.98      inference(renaming,[status(thm)],[c_3268]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3725,plain,
% 2.99/0.98      ( v3_pre_topc(X0_51,sK2) = iProver_top
% 2.99/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.99/0.98      | r2_hidden(X0_51,u1_pre_topc(sK2)) != iProver_top ),
% 2.99/0.98      inference(demodulation,[status(thm)],[c_3587,c_3269]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_6906,plain,
% 2.99/0.98      ( v3_pre_topc(sK0(sK1,sK3,sK4),sK2) = iProver_top
% 2.99/0.98      | r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK2)) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_6898,c_3725]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1,plain,
% 2.99/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.99/0.98      | ~ r2_hidden(X2,X0)
% 2.99/0.98      | r2_hidden(X2,X1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2451,plain,
% 2.99/0.98      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 2.99/0.98      | ~ r2_hidden(X2_51,X0_51)
% 2.99/0.98      | r2_hidden(X2_51,X1_51) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_5446,plain,
% 2.99/0.98      ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(X0_51))
% 2.99/0.98      | r2_hidden(sK0(sK1,sK3,sK4),X0_51)
% 2.99/0.98      | ~ r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK3)) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_2451]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_6593,plain,
% 2.99/0.98      ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(u1_pre_topc(sK2)))
% 2.99/0.98      | r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK2))
% 2.99/0.98      | ~ r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK3)) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_5446]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_6594,plain,
% 2.99/0.98      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(u1_pre_topc(sK2))) != iProver_top
% 2.99/0.98      | r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK2)) = iProver_top
% 2.99/0.98      | r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK3)) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_6593]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_5,plain,
% 2.99/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.99/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.99/0.98      | r2_hidden(X0,u1_pre_topc(X1))
% 2.99/0.98      | ~ l1_pre_topc(X1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2449,plain,
% 2.99/0.98      ( ~ v3_pre_topc(X0_51,X0_52)
% 2.99/0.98      | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52)))
% 2.99/0.98      | r2_hidden(X0_51,u1_pre_topc(X0_52))
% 2.99/0.98      | ~ l1_pre_topc(X0_52) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4592,plain,
% 2.99/0.98      ( ~ v3_pre_topc(sK0(sK1,sK3,sK4),sK3)
% 2.99/0.98      | ~ m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.99/0.98      | r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK3))
% 2.99/0.98      | ~ l1_pre_topc(sK3) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_2449]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4598,plain,
% 2.99/0.98      ( v3_pre_topc(sK0(sK1,sK3,sK4),sK3) != iProver_top
% 2.99/0.98      | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.99/0.98      | r2_hidden(sK0(sK1,sK3,sK4),u1_pre_topc(sK3)) = iProver_top
% 2.99/0.98      | l1_pre_topc(sK3) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_4592]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4147,plain,
% 2.99/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
% 2.99/0.98      | v5_pre_topc(sK4,sK1,sK3)
% 2.99/0.98      | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.99/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
% 2.99/0.98      | ~ l1_pre_topc(sK3)
% 2.99/0.98      | ~ l1_pre_topc(sK1)
% 2.99/0.98      | k2_struct_0(sK3) = k1_xboole_0 ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_2433]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_4151,plain,
% 2.99/0.98      ( k2_struct_0(sK3) = k1_xboole_0
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,sK1,sK3) = iProver_top
% 2.99/0.98      | m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK3) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_4147]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_11,plain,
% 2.99/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.98      | v5_pre_topc(X0,X1,X2)
% 2.99/0.98      | v3_pre_topc(sK0(X1,X2,X0),X2)
% 2.99/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.98      | ~ v1_funct_1(X0)
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | ~ l1_pre_topc(X2)
% 2.99/0.98      | k2_struct_0(X2) = k1_xboole_0 ),
% 2.99/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_512,plain,
% 2.99/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.98      | v5_pre_topc(X0,X1,X2)
% 2.99/0.98      | v3_pre_topc(sK0(X1,X2,X0),X2)
% 2.99/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | ~ l1_pre_topc(X2)
% 2.99/0.98      | k2_struct_0(X2) = k1_xboole_0
% 2.99/0.98      | sK4 != X0 ),
% 2.99/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_513,plain,
% 2.99/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 2.99/0.98      | v5_pre_topc(sK4,X0,X1)
% 2.99/0.98      | v3_pre_topc(sK0(X0,X1,sK4),X1)
% 2.99/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.99/0.98      | ~ l1_pre_topc(X0)
% 2.99/0.98      | ~ l1_pre_topc(X1)
% 2.99/0.98      | k2_struct_0(X1) = k1_xboole_0 ),
% 2.99/0.98      inference(unflattening,[status(thm)],[c_512]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2431,plain,
% 2.99/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 2.99/0.98      | v5_pre_topc(sK4,X0_52,X1_52)
% 2.99/0.98      | v3_pre_topc(sK0(X0_52,X1_52,sK4),X1_52)
% 2.99/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 2.99/0.98      | ~ l1_pre_topc(X0_52)
% 2.99/0.98      | ~ l1_pre_topc(X1_52)
% 2.99/0.98      | k2_struct_0(X1_52) = k1_xboole_0 ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_513]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2862,plain,
% 2.99/0.98      ( k2_struct_0(X0_52) = k1_xboole_0
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,X1_52,X0_52) = iProver_top
% 2.99/0.98      | v3_pre_topc(sK0(X1_52,X0_52,sK4),X0_52) = iProver_top
% 2.99/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 2.99/0.98      | l1_pre_topc(X1_52) != iProver_top
% 2.99/0.98      | l1_pre_topc(X0_52) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2431]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3462,plain,
% 2.99/0.98      ( k2_struct_0(sK3) = k1_xboole_0
% 2.99/0.98      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top
% 2.99/0.98      | v5_pre_topc(sK4,sK1,sK3) = iProver_top
% 2.99/0.98      | v3_pre_topc(sK0(sK1,sK3,sK4),sK3) = iProver_top
% 2.99/0.98      | l1_pre_topc(sK3) != iProver_top
% 2.99/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_2886,c_2862]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2,plain,
% 2.99/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.99/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_21,negated_conjecture,
% 2.99/0.98      ( r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2)) ),
% 2.99/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_306,plain,
% 2.99/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.99/0.98      | u1_pre_topc(sK2) != X1
% 2.99/0.98      | u1_pre_topc(sK3) != X0 ),
% 2.99/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_21]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_307,plain,
% 2.99/0.98      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(u1_pre_topc(sK2))) ),
% 2.99/0.98      inference(unflattening,[status(thm)],[c_306]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_308,plain,
% 2.99/0.98      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(u1_pre_topc(sK2))) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_18,negated_conjecture,
% 2.99/0.98      ( v5_pre_topc(sK4,sK1,sK2) ),
% 2.99/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_38,plain,
% 2.99/0.98      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(contradiction,plain,
% 2.99/0.98      ( $false ),
% 2.99/0.98      inference(minisat,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_8145,c_6906,c_6594,c_5067,c_4598,c_4151,c_3727,c_3726,
% 2.99/0.98                 c_3462,c_3259,c_3155,c_3154,c_2881,c_2918,c_2886,c_2438,
% 2.99/0.98                 c_2475,c_308,c_38,c_34,c_23,c_30]) ).
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.99/0.98  
% 2.99/0.98  ------                               Statistics
% 2.99/0.98  
% 2.99/0.98  ------ General
% 2.99/0.98  
% 2.99/0.98  abstr_ref_over_cycles:                  0
% 2.99/0.98  abstr_ref_under_cycles:                 0
% 2.99/0.98  gc_basic_clause_elim:                   0
% 2.99/0.98  forced_gc_time:                         0
% 2.99/0.98  parsing_time:                           0.011
% 2.99/0.98  unif_index_cands_time:                  0.
% 2.99/0.98  unif_index_add_time:                    0.
% 2.99/0.98  orderings_time:                         0.
% 2.99/0.98  out_proof_time:                         0.012
% 2.99/0.98  total_time:                             0.241
% 2.99/0.98  num_of_symbols:                         57
% 2.99/0.98  num_of_terms:                           3140
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing
% 2.99/0.98  
% 2.99/0.98  num_of_splits:                          0
% 2.99/0.98  num_of_split_atoms:                     0
% 2.99/0.98  num_of_reused_defs:                     0
% 2.99/0.98  num_eq_ax_congr_red:                    23
% 2.99/0.98  num_of_sem_filtered_clauses:            1
% 2.99/0.98  num_of_subtypes:                        3
% 2.99/0.98  monotx_restored_types:                  0
% 2.99/0.98  sat_num_of_epr_types:                   0
% 2.99/0.98  sat_num_of_non_cyclic_types:            0
% 2.99/0.98  sat_guarded_non_collapsed_types:        0
% 2.99/0.98  num_pure_diseq_elim:                    0
% 2.99/0.98  simp_replaced_by:                       0
% 2.99/0.98  res_preprocessed:                       126
% 2.99/0.98  prep_upred:                             0
% 2.99/0.98  prep_unflattend:                        45
% 2.99/0.98  smt_new_axioms:                         0
% 2.99/0.98  pred_elim_cands:                        6
% 2.99/0.98  pred_elim:                              5
% 2.99/0.98  pred_elim_cl:                           5
% 2.99/0.98  pred_elim_cycles:                       9
% 2.99/0.98  merged_defs:                            0
% 2.99/0.98  merged_defs_ncl:                        0
% 2.99/0.98  bin_hyper_res:                          0
% 2.99/0.98  prep_cycles:                            4
% 2.99/0.98  pred_elim_time:                         0.044
% 2.99/0.98  splitting_time:                         0.
% 2.99/0.98  sem_filter_time:                        0.
% 2.99/0.98  monotx_time:                            0.
% 2.99/0.98  subtype_inf_time:                       0.
% 2.99/0.98  
% 2.99/0.98  ------ Problem properties
% 2.99/0.98  
% 2.99/0.98  clauses:                                24
% 2.99/0.98  conjectures:                            8
% 2.99/0.98  epr:                                    4
% 2.99/0.98  horn:                                   18
% 2.99/0.98  ground:                                 12
% 2.99/0.98  unary:                                  11
% 2.99/0.98  binary:                                 1
% 2.99/0.98  lits:                                   87
% 2.99/0.98  lits_eq:                                13
% 2.99/0.98  fd_pure:                                0
% 2.99/0.98  fd_pseudo:                              0
% 2.99/0.98  fd_cond:                                0
% 2.99/0.98  fd_pseudo_cond:                         0
% 2.99/0.98  ac_symbols:                             0
% 2.99/0.98  
% 2.99/0.98  ------ Propositional Solver
% 2.99/0.98  
% 2.99/0.98  prop_solver_calls:                      33
% 2.99/0.98  prop_fast_solver_calls:                 2099
% 2.99/0.98  smt_solver_calls:                       0
% 2.99/0.98  smt_fast_solver_calls:                  0
% 2.99/0.98  prop_num_of_clauses:                    1747
% 2.99/0.98  prop_preprocess_simplified:             5470
% 2.99/0.98  prop_fo_subsumed:                       131
% 2.99/0.98  prop_solver_time:                       0.
% 2.99/0.98  smt_solver_time:                        0.
% 2.99/0.98  smt_fast_solver_time:                   0.
% 2.99/0.98  prop_fast_solver_time:                  0.
% 2.99/0.98  prop_unsat_core_time:                   0.
% 2.99/0.98  
% 2.99/0.98  ------ QBF
% 2.99/0.98  
% 2.99/0.98  qbf_q_res:                              0
% 2.99/0.98  qbf_num_tautologies:                    0
% 2.99/0.98  qbf_prep_cycles:                        0
% 2.99/0.98  
% 2.99/0.98  ------ BMC1
% 2.99/0.98  
% 2.99/0.98  bmc1_current_bound:                     -1
% 2.99/0.98  bmc1_last_solved_bound:                 -1
% 2.99/0.98  bmc1_unsat_core_size:                   -1
% 2.99/0.98  bmc1_unsat_core_parents_size:           -1
% 2.99/0.98  bmc1_merge_next_fun:                    0
% 2.99/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.99/0.98  
% 2.99/0.98  ------ Instantiation
% 2.99/0.98  
% 2.99/0.98  inst_num_of_clauses:                    621
% 2.99/0.98  inst_num_in_passive:                    156
% 2.99/0.98  inst_num_in_active:                     451
% 2.99/0.98  inst_num_in_unprocessed:                14
% 2.99/0.98  inst_num_of_loops:                      470
% 2.99/0.98  inst_num_of_learning_restarts:          0
% 2.99/0.98  inst_num_moves_active_passive:          11
% 2.99/0.98  inst_lit_activity:                      0
% 2.99/0.98  inst_lit_activity_moves:                0
% 2.99/0.98  inst_num_tautologies:                   0
% 2.99/0.98  inst_num_prop_implied:                  0
% 2.99/0.98  inst_num_existing_simplified:           0
% 2.99/0.98  inst_num_eq_res_simplified:             0
% 2.99/0.98  inst_num_child_elim:                    0
% 2.99/0.98  inst_num_of_dismatching_blockings:      173
% 2.99/0.98  inst_num_of_non_proper_insts:           965
% 2.99/0.98  inst_num_of_duplicates:                 0
% 2.99/0.98  inst_inst_num_from_inst_to_res:         0
% 2.99/0.98  inst_dismatching_checking_time:         0.
% 2.99/0.98  
% 2.99/0.98  ------ Resolution
% 2.99/0.98  
% 2.99/0.98  res_num_of_clauses:                     0
% 2.99/0.98  res_num_in_passive:                     0
% 2.99/0.98  res_num_in_active:                      0
% 2.99/0.98  res_num_of_loops:                       130
% 2.99/0.98  res_forward_subset_subsumed:            216
% 2.99/0.98  res_backward_subset_subsumed:           0
% 2.99/0.98  res_forward_subsumed:                   0
% 2.99/0.98  res_backward_subsumed:                  0
% 2.99/0.98  res_forward_subsumption_resolution:     0
% 2.99/0.98  res_backward_subsumption_resolution:    0
% 2.99/0.98  res_clause_to_clause_subsumption:       469
% 2.99/0.98  res_orphan_elimination:                 0
% 2.99/0.98  res_tautology_del:                      164
% 2.99/0.98  res_num_eq_res_simplified:              0
% 2.99/0.98  res_num_sel_changes:                    0
% 2.99/0.98  res_moves_from_active_to_pass:          0
% 2.99/0.98  
% 2.99/0.98  ------ Superposition
% 2.99/0.98  
% 2.99/0.98  sup_time_total:                         0.
% 2.99/0.98  sup_time_generating:                    0.
% 2.99/0.98  sup_time_sim_full:                      0.
% 2.99/0.98  sup_time_sim_immed:                     0.
% 2.99/0.98  
% 2.99/0.98  sup_num_of_clauses:                     97
% 2.99/0.98  sup_num_in_active:                      82
% 2.99/0.98  sup_num_in_passive:                     15
% 2.99/0.98  sup_num_of_loops:                       92
% 2.99/0.98  sup_fw_superposition:                   91
% 2.99/0.98  sup_bw_superposition:                   28
% 2.99/0.98  sup_immediate_simplified:               89
% 2.99/0.98  sup_given_eliminated:                   0
% 2.99/0.98  comparisons_done:                       0
% 2.99/0.98  comparisons_avoided:                    0
% 2.99/0.98  
% 2.99/0.98  ------ Simplifications
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  sim_fw_subset_subsumed:                 18
% 2.99/0.98  sim_bw_subset_subsumed:                 0
% 2.99/0.98  sim_fw_subsumed:                        18
% 2.99/0.98  sim_bw_subsumed:                        0
% 2.99/0.98  sim_fw_subsumption_res:                 2
% 2.99/0.98  sim_bw_subsumption_res:                 0
% 2.99/0.98  sim_tautology_del:                      6
% 2.99/0.98  sim_eq_tautology_del:                   0
% 2.99/0.98  sim_eq_res_simp:                        0
% 2.99/0.98  sim_fw_demodulated:                     9
% 2.99/0.98  sim_bw_demodulated:                     11
% 2.99/0.98  sim_light_normalised:                   81
% 2.99/0.98  sim_joinable_taut:                      0
% 2.99/0.98  sim_joinable_simp:                      0
% 2.99/0.98  sim_ac_normalised:                      0
% 2.99/0.98  sim_smt_subsumption:                    0
% 2.99/0.98  
%------------------------------------------------------------------------------
