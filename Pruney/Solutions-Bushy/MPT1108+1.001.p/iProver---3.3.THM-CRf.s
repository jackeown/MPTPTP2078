%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1108+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:54 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 495 expanded)
%              Number of clauses        :   76 ( 143 expanded)
%              Number of leaves         :   14 ( 160 expanded)
%              Depth                    :   18
%              Number of atoms          :  430 (3667 expanded)
%              Number of equality atoms :  122 ( 193 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                    & v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                    & v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                      & v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                      & v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                    | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                    | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
            | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
            | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,sK3)),u1_struct_0(X1))))
          | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3),u1_struct_0(k1_pre_topc(X0,sK3)),u1_struct_0(X1))
          | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
              | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
              | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3)) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                    | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(sK1))))
                  | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(sK1))
                  | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3)) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(X1))))
                    | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))))
      | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))
      | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f30,f29,f28,f27])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_554,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_857,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ v1_funct_1(X0_48)
    | k2_partfun1(X1_48,X2_48,X0_48,X3_48) = k7_relat_1(X0_48,X3_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_853,plain,
    ( k2_partfun1(X0_48,X1_48,X2_48,X3_48) = k7_relat_1(X2_48,X3_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X2_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_1336,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_48) = k7_relat_1(sK2,X0_48)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_853])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ v1_funct_1(sK2)
    | k2_partfun1(X0_48,X1_48,sK2,X2_48) = k7_relat_1(sK2,X2_48) ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_1113,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_48) = k7_relat_1(sK2,X0_48) ),
    inference(instantiation,[status(thm)],[c_1021])).

cnf(c_1493,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_48) = k7_relat_1(sK2,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1336,c_19,c_17,c_1113])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_partfun1(X1,X2,X0,X3),X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_367,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_partfun1(X1,X2,X0,X3),X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | X5 != X1
    | X4 != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_368,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_partfun1(X1,X2,X0,X3),X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_546,plain,
    ( ~ v1_funct_2(X0_48,X1_48,X2_48)
    | v1_funct_2(k2_partfun1(X1_48,X2_48,X0_48,X3_48),X3_48,X2_48)
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(X1_48))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ v1_funct_1(X0_48)
    | k1_xboole_0 = X2_48 ),
    inference(subtyping,[status(esa)],[c_368])).

cnf(c_864,plain,
    ( k1_xboole_0 = X0_48
    | v1_funct_2(X1_48,X2_48,X0_48) != iProver_top
    | v1_funct_2(k2_partfun1(X2_48,X0_48,X1_48,X3_48),X3_48,X0_48) = iProver_top
    | m1_subset_1(X3_48,k1_zfmisc_1(X2_48)) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X0_48))) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_3315,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k7_relat_1(sK2,X0_48),X0_48,u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1493,c_864])).

cnf(c_26,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_27,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_254,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_272,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_254,c_21])).

cnf(c_273,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_285,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(sK1) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_273])).

cnf(c_286,plain,
    ( ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_288,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_286,c_20])).

cnf(c_551,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_288])).

cnf(c_3755,plain,
    ( v1_funct_2(k7_relat_1(sK2,X0_48),X0_48,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3315,c_26,c_27,c_28,c_551])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_391,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X2)))
    | ~ v1_funct_1(X0)
    | X4 != X1
    | X3 != X5
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_392,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_545,plain,
    ( ~ v1_funct_2(X0_48,X1_48,X2_48)
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(X1_48))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | m1_subset_1(k2_partfun1(X1_48,X2_48,X0_48,X3_48),k1_zfmisc_1(k2_zfmisc_1(X3_48,X2_48)))
    | ~ v1_funct_1(X0_48)
    | k1_xboole_0 = X2_48 ),
    inference(subtyping,[status(esa)],[c_392])).

cnf(c_865,plain,
    ( k1_xboole_0 = X0_48
    | v1_funct_2(X1_48,X2_48,X0_48) != iProver_top
    | m1_subset_1(X3_48,k1_zfmisc_1(X2_48)) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X0_48))) != iProver_top
    | m1_subset_1(k2_partfun1(X2_48,X0_48,X1_48,X3_48),k1_zfmisc_1(k2_zfmisc_1(X3_48,X0_48))) = iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_4444,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK2,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1493,c_865])).

cnf(c_5278,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK2,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4444,c_26,c_27,c_28,c_551])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_555,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_856,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_549,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k1_pre_topc(sK0,X0_48)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_307])).

cnf(c_861,plain,
    ( u1_struct_0(k1_pre_topc(sK0,X0_48)) = X0_48
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_549])).

cnf(c_1135,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_856,c_861])).

cnf(c_15,negated_conjecture,
    ( ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_556,negated_conjecture,
    ( ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_855,plain,
    ( v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_1443,plain,
    ( v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1135,c_855])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k5_relset_1(X1_48,X2_48,X0_48,X3_48) = k7_relat_1(X0_48,X3_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_854,plain,
    ( k5_relset_1(X0_48,X1_48,X2_48,X3_48) = k7_relat_1(X2_48,X3_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_557])).

cnf(c_1222,plain,
    ( k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_48) = k7_relat_1(sK2,X0_48) ),
    inference(superposition,[status(thm)],[c_857,c_854])).

cnf(c_1572,plain,
    ( v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1443,c_1222])).

cnf(c_5294,plain,
    ( v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5278,c_1572])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5431,plain,
    ( v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5294,c_29])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_partfun1(X1_48,X2_48,X0_48,X3_48)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_852,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_partfun1(X1_48,X2_48,X0_48,X3_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_559])).

cnf(c_1312,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_48)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_852])).

cnf(c_1001,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | v1_funct_1(k2_partfun1(X0_48,X1_48,sK2,X2_48))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_1108,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_48))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_1109,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_48)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1108])).

cnf(c_1485,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_48)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1312,c_26,c_28,c_1109])).

cnf(c_1497,plain,
    ( v1_funct_1(k7_relat_1(sK2,X0_48)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1493,c_1485])).

cnf(c_5437,plain,
    ( v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5431,c_1497])).

cnf(c_5439,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3755,c_5437])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5439,c_29])).


%------------------------------------------------------------------------------
