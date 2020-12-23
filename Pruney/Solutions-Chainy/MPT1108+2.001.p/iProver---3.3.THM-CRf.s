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
% DateTime   : Thu Dec  3 12:11:23 EST 2020

% Result     : Theorem 6.60s
% Output     : CNFRefutation 6.60s
% Verified   : 
% Statistics : Number of formulae       :  303 (4610 expanded)
%              Number of clauses        :  188 (1403 expanded)
%              Number of leaves         :   31 (1263 expanded)
%              Depth                    :   25
%              Number of atoms          :  976 (27841 expanded)
%              Number of equality atoms :  455 (3435 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f70])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f71,f72])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f67,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f66])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f67,f68])).

fof(f85,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f28,conjecture,(
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

fof(f29,negated_conjecture,(
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
    inference(negated_conjecture,[],[f28])).

fof(f30,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                      & v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                      & v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f29])).

fof(f64,plain,(
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
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f65,plain,(
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
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
            | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
            | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,sK5)),u1_struct_0(X1))))
          | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5),u1_struct_0(k1_pre_topc(X0,sK5)),u1_struct_0(X1))
          | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
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
            ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
              | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
              | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X3)) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
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
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(sK3))))
                  | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(sK3))
                  | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X3)) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,
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
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X3)),u1_struct_0(X1))))
                    | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(sK2,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,
    ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
      | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))
      | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f65,f83,f82,f81,f80])).

fof(f136,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f84])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f74])).

fof(f92,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f135,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f84])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f23,axiom,(
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

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f79,plain,(
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
    inference(nnf_transformation,[],[f56])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f134,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f84])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f144,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f122])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f76])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f140,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f96])).

fof(f86,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f59])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f133,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f61])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f137,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
    inference(cnf_transformation,[],[f84])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f130,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f131,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f145,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f121])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f141,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f95])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f142,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f123])).

fof(f143,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f142])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f106,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2269,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2258,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3573,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2269,c_2258])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2267,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3396,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2269,c_2267])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2263,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12522,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3396,c_2263])).

cnf(c_19722,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3573,c_12522])).

cnf(c_26,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_18,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_26,c_18])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_616,c_26,c_25,c_18])).

cnf(c_2247,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_3508,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2269,c_2247])).

cnf(c_19727,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19722,c_3508])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2274,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2276,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3555,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2274,c_2276])).

cnf(c_47,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_2251,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_3397,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2251,c_2267])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2272,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5394,plain,
    ( u1_struct_0(sK2) = sK5
    | r1_tarski(u1_struct_0(sK2),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3397,c_2272])).

cnf(c_18274,plain,
    ( u1_struct_0(sK2) = sK5
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_5394])).

cnf(c_48,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_2250,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2257,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4058,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2250,c_2257])).

cnf(c_38,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_49,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_760,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | u1_struct_0(sK3) != X2
    | u1_struct_0(sK2) != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_49])).

cnf(c_761,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = u1_struct_0(sK2)
    | k1_xboole_0 = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_760])).

cnf(c_763,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = u1_struct_0(sK2)
    | k1_xboole_0 = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_761,c_48])).

cnf(c_4153,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(sK2) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_4058,c_763])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f144])).

cnf(c_799,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | u1_struct_0(sK3) != k1_xboole_0
    | u1_struct_0(sK2) != X1
    | sK4 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_49])).

cnf(c_800,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | u1_struct_0(sK3) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK2)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_799])).

cnf(c_2239,plain,
    ( u1_struct_0(sK3) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK2)
    | k1_xboole_0 = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_2439,plain,
    ( u1_struct_0(sK3) != k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2239,c_9])).

cnf(c_4247,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4153,c_2439])).

cnf(c_4256,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4153,c_2250])).

cnf(c_4259,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4256,c_9])).

cnf(c_4322,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4247,c_4259])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_168,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_170,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2907,plain,
    ( ~ r1_tarski(X0,sK0(X0))
    | ~ r2_hidden(sK0(X0),X0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2908,plain,
    ( r1_tarski(X0,sK0(X0)) != iProver_top
    | r2_hidden(sK0(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2907])).

cnf(c_2910,plain,
    ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) != iProver_top
    | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2908])).

cnf(c_3328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0(X0)))
    | r1_tarski(X0,sK0(X0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3329,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0(X0))) != iProver_top
    | r1_tarski(X0,sK0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3328])).

cnf(c_3331,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(k1_xboole_0))) != iProver_top
    | r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3329])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_6548,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK4)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6549,plain,
    ( sK4 = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6548])).

cnf(c_6551,plain,
    ( sK4 = k1_xboole_0
    | v1_xboole_0(sK4) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6549])).

cnf(c_7412,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_7415,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(k1_xboole_0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7412])).

cnf(c_2277,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3398,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2250,c_2267])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2273,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7697,plain,
    ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3398,c_2273])).

cnf(c_7899,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7697,c_2276])).

cnf(c_11045,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK4)
    | r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4153,c_7899])).

cnf(c_11046,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK4)
    | r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11045,c_9])).

cnf(c_11292,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | u1_struct_0(sK2) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11046,c_170,c_2910,c_3331,c_7415])).

cnf(c_11293,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK4)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_11292])).

cnf(c_11298,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK4)
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2277,c_11293])).

cnf(c_15269,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4322,c_170,c_2910,c_3331,c_6551,c_7415,c_11298])).

cnf(c_3509,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
    inference(superposition,[status(thm)],[c_2250,c_2247])).

cnf(c_15318,plain,
    ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15269,c_3509])).

cnf(c_41,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_2252,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_3915,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2250,c_2252])).

cnf(c_50,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_2719,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_4156,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3915,c_50,c_48,c_2719])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_2254,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_5281,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4156,c_2254])).

cnf(c_55,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_57,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_6070,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5281,c_55,c_57])).

cnf(c_6084,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_6070,c_2257])).

cnf(c_15702,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k1_relat_1(k7_relat_1(sK4,k1_relat_1(sK4)))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15318,c_6084])).

cnf(c_15723,plain,
    ( k1_relat_1(k7_relat_1(sK4,k1_relat_1(sK4))) = k1_relat_1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_15702,c_4058])).

cnf(c_2649,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2650,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2649])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2256,plain,
    ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5619,plain,
    ( k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_2250,c_2256])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k5_relset_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2255,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k5_relset_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6186,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5619,c_2255])).

cnf(c_6659,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6186,c_57])).

cnf(c_6674,plain,
    ( k1_relset_1(X0,u1_struct_0(sK3),k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_6659,c_2257])).

cnf(c_43,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f128])).

cnf(c_46,negated_conjecture,
    ( ~ v1_funct_2(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_728,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | u1_struct_0(k1_pre_topc(sK2,sK5)) != X1
    | u1_struct_0(sK3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_46])).

cnf(c_729,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k1_relset_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3),k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != u1_struct_0(k1_pre_topc(sK2,sK5)) ),
    inference(unflattening,[status(thm)],[c_728])).

cnf(c_2242,plain,
    ( k1_relset_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3),k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != u1_struct_0(k1_pre_topc(sK2,sK5))
    | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_45,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_52,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_45,c_52])).

cnf(c_649,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(k1_pre_topc(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_2245,plain,
    ( u1_struct_0(k1_pre_topc(sK2,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_2666,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_2251,c_2245])).

cnf(c_2728,plain,
    ( k1_relset_1(sK5,u1_struct_0(sK3),k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != sK5
    | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2242,c_2666])).

cnf(c_5659,plain,
    ( k1_relset_1(sK5,u1_struct_0(sK3),k7_relat_1(sK4,sK5)) != sK5
    | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5619,c_2728])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2792,plain,
    ( v1_funct_1(k7_relat_1(sK4,X0))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_4933,plain,
    ( v1_funct_1(k7_relat_1(sK4,sK5))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2792])).

cnf(c_4934,plain,
    ( v1_funct_1(k7_relat_1(sK4,sK5)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4933])).

cnf(c_6128,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
    | k1_relset_1(sK5,u1_struct_0(sK3),k7_relat_1(sK4,sK5)) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5659,c_55,c_57,c_2650,c_4934])).

cnf(c_6129,plain,
    ( k1_relset_1(sK5,u1_struct_0(sK3),k7_relat_1(sK4,sK5)) != sK5
    | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6128])).

cnf(c_8572,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK5)) != sK5
    | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6674,c_6129])).

cnf(c_12358,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK5)) != sK5 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8572,c_6659])).

cnf(c_15320,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK5,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15269,c_3397])).

cnf(c_16015,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK5)) = sK5
    | sK4 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_15320,c_2263])).

cnf(c_16231,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15723,c_57,c_2650,c_12358,c_16015])).

cnf(c_35,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f145])).

cnf(c_815,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | u1_struct_0(k1_pre_topc(sK2,sK5)) != k1_xboole_0
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_46])).

cnf(c_816,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK3))))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k1_xboole_0
    | u1_struct_0(k1_pre_topc(sK2,sK5)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_815])).

cnf(c_2238,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k1_xboole_0
    | u1_struct_0(k1_pre_topc(sK2,sK5)) != k1_xboole_0
    | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f141])).

cnf(c_2505,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k1_xboole_0
    | u1_struct_0(k1_pre_topc(sK2,sK5)) != k1_xboole_0
    | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2238,c_10])).

cnf(c_3048,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k1_xboole_0
    | sK5 != k1_xboole_0
    | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2505,c_2666])).

cnf(c_5656,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k7_relat_1(sK4,sK5)) != k1_xboole_0
    | sK5 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5619,c_3048])).

cnf(c_7236,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
    | sK5 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k7_relat_1(sK4,sK5)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5656,c_55,c_57,c_2650,c_4934])).

cnf(c_7237,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k7_relat_1(sK4,sK5)) != k1_xboole_0
    | sK5 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7236])).

cnf(c_7244,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k7_relat_1(sK4,sK5)) != k1_xboole_0
    | sK5 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7237,c_6659])).

cnf(c_16293,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k7_relat_1(k1_xboole_0,sK5)) != k1_xboole_0
    | sK5 != k1_xboole_0
    | m1_subset_1(k7_relat_1(k1_xboole_0,sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16231,c_7244])).

cnf(c_4056,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2269,c_2257])).

cnf(c_16442,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | sK5 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16293,c_3508,c_4056])).

cnf(c_33,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f143])).

cnf(c_775,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k1_xboole_0
    | u1_struct_0(k1_pre_topc(sK2,sK5)) != X0
    | u1_struct_0(sK3) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_46])).

cnf(c_776,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),k1_xboole_0)))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k1_xboole_0
    | u1_struct_0(sK3) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(k1_pre_topc(sK2,sK5)) ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_790,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k1_xboole_0
    | u1_struct_0(sK3) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(k1_pre_topc(sK2,sK5)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_776,c_12])).

cnf(c_2240,plain,
    ( k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k1_xboole_0
    | u1_struct_0(sK3) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(k1_pre_topc(sK2,sK5))
    | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_3039,plain,
    ( k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k1_xboole_0
    | u1_struct_0(k1_pre_topc(sK2,sK5)) = k1_xboole_0
    | u1_struct_0(sK3) != k1_xboole_0
    | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2240,c_2666])).

cnf(c_3040,plain,
    ( k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k1_xboole_0
    | u1_struct_0(sK3) != k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3039,c_2666])).

cnf(c_5657,plain,
    ( k7_relat_1(sK4,sK5) != k1_xboole_0
    | u1_struct_0(sK3) != k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5619,c_3040])).

cnf(c_6833,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
    | sK5 = k1_xboole_0
    | u1_struct_0(sK3) != k1_xboole_0
    | k7_relat_1(sK4,sK5) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5657,c_55,c_57,c_2650,c_4934])).

cnf(c_6834,plain,
    ( k7_relat_1(sK4,sK5) != k1_xboole_0
    | u1_struct_0(sK3) != k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6833])).

cnf(c_6841,plain,
    ( k7_relat_1(sK4,sK5) != k1_xboole_0
    | u1_struct_0(sK3) != k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6834,c_6659])).

cnf(c_16295,plain,
    ( k7_relat_1(k1_xboole_0,sK5) != k1_xboole_0
    | u1_struct_0(sK3) != k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16231,c_6841])).

cnf(c_16428,plain,
    ( u1_struct_0(sK3) != k1_xboole_0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16295,c_3508])).

cnf(c_16429,plain,
    ( u1_struct_0(sK3) != k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_16428])).

cnf(c_847,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != sK4
    | u1_struct_0(k1_pre_topc(sK2,sK5)) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_46,c_49])).

cnf(c_956,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != sK4
    | u1_struct_0(k1_pre_topc(sK2,sK5)) != u1_struct_0(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_847])).

cnf(c_2236,plain,
    ( k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != sK4
    | u1_struct_0(k1_pre_topc(sK2,sK5)) != u1_struct_0(sK2)
    | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_2991,plain,
    ( k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != sK4
    | u1_struct_0(sK2) != sK5
    | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2236,c_2666])).

cnf(c_5658,plain,
    ( k7_relat_1(sK4,sK5) != sK4
    | u1_struct_0(sK2) != sK5
    | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5619,c_2991])).

cnf(c_6711,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
    | u1_struct_0(sK2) != sK5
    | k7_relat_1(sK4,sK5) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5658,c_55,c_57,c_2650,c_4934])).

cnf(c_6712,plain,
    ( k7_relat_1(sK4,sK5) != sK4
    | u1_struct_0(sK2) != sK5
    | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6711])).

cnf(c_6718,plain,
    ( k7_relat_1(sK4,sK5) != sK4
    | u1_struct_0(sK2) != sK5 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6712,c_6659])).

cnf(c_16296,plain,
    ( k7_relat_1(k1_xboole_0,sK5) != k1_xboole_0
    | u1_struct_0(sK2) != sK5 ),
    inference(demodulation,[status(thm)],[c_16231,c_6718])).

cnf(c_16422,plain,
    ( u1_struct_0(sK2) != sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16296,c_3508])).

cnf(c_16423,plain,
    ( u1_struct_0(sK2) != sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_16422])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_21,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31,c_21])).

cnf(c_291,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_290])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | u1_struct_0(sK3) != X2
    | u1_struct_0(sK2) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_291,c_49])).

cnf(c_744,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_746,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_xboole_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_744,c_48])).

cnf(c_2241,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_2270,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4049,plain,
    ( u1_struct_0(sK3) = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2241,c_2270])).

cnf(c_4051,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(sK4) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4049])).

cnf(c_1289,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2753,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1289])).

cnf(c_2754,plain,
    ( sK4 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2753])).

cnf(c_2756,plain,
    ( sK4 != k1_xboole_0
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2754])).

cnf(c_147,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_149,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19727,c_18274,c_16442,c_16429,c_16423,c_16015,c_12358,c_7415,c_4051,c_3331,c_2910,c_2756,c_2650,c_170,c_149,c_57])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 6.60/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.60/1.51  
% 6.60/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.60/1.51  
% 6.60/1.51  ------  iProver source info
% 6.60/1.51  
% 6.60/1.51  git: date: 2020-06-30 10:37:57 +0100
% 6.60/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.60/1.51  git: non_committed_changes: false
% 6.60/1.51  git: last_make_outside_of_git: false
% 6.60/1.51  
% 6.60/1.51  ------ 
% 6.60/1.51  
% 6.60/1.51  ------ Input Options
% 6.60/1.51  
% 6.60/1.51  --out_options                           all
% 6.60/1.51  --tptp_safe_out                         true
% 6.60/1.51  --problem_path                          ""
% 6.60/1.51  --include_path                          ""
% 6.60/1.51  --clausifier                            res/vclausify_rel
% 6.60/1.51  --clausifier_options                    --mode clausify
% 6.60/1.51  --stdin                                 false
% 6.60/1.51  --stats_out                             all
% 6.60/1.51  
% 6.60/1.51  ------ General Options
% 6.60/1.51  
% 6.60/1.51  --fof                                   false
% 6.60/1.51  --time_out_real                         305.
% 6.60/1.51  --time_out_virtual                      -1.
% 6.60/1.51  --symbol_type_check                     false
% 6.60/1.51  --clausify_out                          false
% 6.60/1.51  --sig_cnt_out                           false
% 6.60/1.51  --trig_cnt_out                          false
% 6.60/1.51  --trig_cnt_out_tolerance                1.
% 6.60/1.51  --trig_cnt_out_sk_spl                   false
% 6.60/1.51  --abstr_cl_out                          false
% 6.60/1.51  
% 6.60/1.51  ------ Global Options
% 6.60/1.51  
% 6.60/1.51  --schedule                              default
% 6.60/1.51  --add_important_lit                     false
% 6.60/1.51  --prop_solver_per_cl                    1000
% 6.60/1.51  --min_unsat_core                        false
% 6.60/1.51  --soft_assumptions                      false
% 6.60/1.51  --soft_lemma_size                       3
% 6.60/1.51  --prop_impl_unit_size                   0
% 6.60/1.51  --prop_impl_unit                        []
% 6.60/1.51  --share_sel_clauses                     true
% 6.60/1.51  --reset_solvers                         false
% 6.60/1.51  --bc_imp_inh                            [conj_cone]
% 6.60/1.51  --conj_cone_tolerance                   3.
% 6.60/1.51  --extra_neg_conj                        none
% 6.60/1.51  --large_theory_mode                     true
% 6.60/1.51  --prolific_symb_bound                   200
% 6.60/1.51  --lt_threshold                          2000
% 6.60/1.51  --clause_weak_htbl                      true
% 6.60/1.51  --gc_record_bc_elim                     false
% 6.60/1.51  
% 6.60/1.51  ------ Preprocessing Options
% 6.60/1.51  
% 6.60/1.51  --preprocessing_flag                    true
% 6.60/1.51  --time_out_prep_mult                    0.1
% 6.60/1.51  --splitting_mode                        input
% 6.60/1.51  --splitting_grd                         true
% 6.60/1.51  --splitting_cvd                         false
% 6.60/1.51  --splitting_cvd_svl                     false
% 6.60/1.51  --splitting_nvd                         32
% 6.60/1.51  --sub_typing                            true
% 6.60/1.51  --prep_gs_sim                           true
% 6.60/1.51  --prep_unflatten                        true
% 6.60/1.51  --prep_res_sim                          true
% 6.60/1.51  --prep_upred                            true
% 6.60/1.51  --prep_sem_filter                       exhaustive
% 6.60/1.51  --prep_sem_filter_out                   false
% 6.60/1.51  --pred_elim                             true
% 6.60/1.51  --res_sim_input                         true
% 6.60/1.51  --eq_ax_congr_red                       true
% 6.60/1.51  --pure_diseq_elim                       true
% 6.60/1.51  --brand_transform                       false
% 6.60/1.51  --non_eq_to_eq                          false
% 6.60/1.51  --prep_def_merge                        true
% 6.60/1.51  --prep_def_merge_prop_impl              false
% 6.60/1.51  --prep_def_merge_mbd                    true
% 6.60/1.51  --prep_def_merge_tr_red                 false
% 6.60/1.51  --prep_def_merge_tr_cl                  false
% 6.60/1.51  --smt_preprocessing                     true
% 6.60/1.51  --smt_ac_axioms                         fast
% 6.60/1.51  --preprocessed_out                      false
% 6.60/1.51  --preprocessed_stats                    false
% 6.60/1.51  
% 6.60/1.51  ------ Abstraction refinement Options
% 6.60/1.51  
% 6.60/1.51  --abstr_ref                             []
% 6.60/1.51  --abstr_ref_prep                        false
% 6.60/1.51  --abstr_ref_until_sat                   false
% 6.60/1.51  --abstr_ref_sig_restrict                funpre
% 6.60/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.60/1.51  --abstr_ref_under                       []
% 6.60/1.51  
% 6.60/1.51  ------ SAT Options
% 6.60/1.51  
% 6.60/1.51  --sat_mode                              false
% 6.60/1.51  --sat_fm_restart_options                ""
% 6.60/1.51  --sat_gr_def                            false
% 6.60/1.51  --sat_epr_types                         true
% 6.60/1.51  --sat_non_cyclic_types                  false
% 6.60/1.51  --sat_finite_models                     false
% 6.60/1.51  --sat_fm_lemmas                         false
% 6.60/1.51  --sat_fm_prep                           false
% 6.60/1.51  --sat_fm_uc_incr                        true
% 6.60/1.51  --sat_out_model                         small
% 6.60/1.51  --sat_out_clauses                       false
% 6.60/1.51  
% 6.60/1.51  ------ QBF Options
% 6.60/1.51  
% 6.60/1.51  --qbf_mode                              false
% 6.60/1.51  --qbf_elim_univ                         false
% 6.60/1.51  --qbf_dom_inst                          none
% 6.60/1.51  --qbf_dom_pre_inst                      false
% 6.60/1.51  --qbf_sk_in                             false
% 6.60/1.51  --qbf_pred_elim                         true
% 6.60/1.51  --qbf_split                             512
% 6.60/1.51  
% 6.60/1.51  ------ BMC1 Options
% 6.60/1.51  
% 6.60/1.51  --bmc1_incremental                      false
% 6.60/1.51  --bmc1_axioms                           reachable_all
% 6.60/1.51  --bmc1_min_bound                        0
% 6.60/1.51  --bmc1_max_bound                        -1
% 6.60/1.51  --bmc1_max_bound_default                -1
% 6.60/1.51  --bmc1_symbol_reachability              true
% 6.60/1.51  --bmc1_property_lemmas                  false
% 6.60/1.51  --bmc1_k_induction                      false
% 6.60/1.51  --bmc1_non_equiv_states                 false
% 6.60/1.51  --bmc1_deadlock                         false
% 6.60/1.51  --bmc1_ucm                              false
% 6.60/1.51  --bmc1_add_unsat_core                   none
% 6.60/1.51  --bmc1_unsat_core_children              false
% 6.60/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.60/1.51  --bmc1_out_stat                         full
% 6.60/1.51  --bmc1_ground_init                      false
% 6.60/1.51  --bmc1_pre_inst_next_state              false
% 6.60/1.51  --bmc1_pre_inst_state                   false
% 6.60/1.51  --bmc1_pre_inst_reach_state             false
% 6.60/1.51  --bmc1_out_unsat_core                   false
% 6.60/1.51  --bmc1_aig_witness_out                  false
% 6.60/1.51  --bmc1_verbose                          false
% 6.60/1.51  --bmc1_dump_clauses_tptp                false
% 6.60/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.60/1.51  --bmc1_dump_file                        -
% 6.60/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.60/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.60/1.51  --bmc1_ucm_extend_mode                  1
% 6.60/1.51  --bmc1_ucm_init_mode                    2
% 6.60/1.51  --bmc1_ucm_cone_mode                    none
% 6.60/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.60/1.51  --bmc1_ucm_relax_model                  4
% 6.60/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.60/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.60/1.51  --bmc1_ucm_layered_model                none
% 6.60/1.51  --bmc1_ucm_max_lemma_size               10
% 6.60/1.51  
% 6.60/1.51  ------ AIG Options
% 6.60/1.51  
% 6.60/1.51  --aig_mode                              false
% 6.60/1.51  
% 6.60/1.51  ------ Instantiation Options
% 6.60/1.51  
% 6.60/1.51  --instantiation_flag                    true
% 6.60/1.51  --inst_sos_flag                         false
% 6.60/1.51  --inst_sos_phase                        true
% 6.60/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.60/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.60/1.51  --inst_lit_sel_side                     num_symb
% 6.60/1.51  --inst_solver_per_active                1400
% 6.60/1.51  --inst_solver_calls_frac                1.
% 6.60/1.51  --inst_passive_queue_type               priority_queues
% 6.60/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.60/1.51  --inst_passive_queues_freq              [25;2]
% 6.60/1.51  --inst_dismatching                      true
% 6.60/1.51  --inst_eager_unprocessed_to_passive     true
% 6.60/1.51  --inst_prop_sim_given                   true
% 6.60/1.51  --inst_prop_sim_new                     false
% 6.60/1.51  --inst_subs_new                         false
% 6.60/1.51  --inst_eq_res_simp                      false
% 6.60/1.51  --inst_subs_given                       false
% 6.60/1.51  --inst_orphan_elimination               true
% 6.60/1.51  --inst_learning_loop_flag               true
% 6.60/1.51  --inst_learning_start                   3000
% 6.60/1.51  --inst_learning_factor                  2
% 6.60/1.51  --inst_start_prop_sim_after_learn       3
% 6.60/1.51  --inst_sel_renew                        solver
% 6.60/1.51  --inst_lit_activity_flag                true
% 6.60/1.51  --inst_restr_to_given                   false
% 6.60/1.51  --inst_activity_threshold               500
% 6.60/1.51  --inst_out_proof                        true
% 6.60/1.51  
% 6.60/1.51  ------ Resolution Options
% 6.60/1.51  
% 6.60/1.51  --resolution_flag                       true
% 6.60/1.51  --res_lit_sel                           adaptive
% 6.60/1.51  --res_lit_sel_side                      none
% 6.60/1.51  --res_ordering                          kbo
% 6.60/1.51  --res_to_prop_solver                    active
% 6.60/1.51  --res_prop_simpl_new                    false
% 6.60/1.51  --res_prop_simpl_given                  true
% 6.60/1.51  --res_passive_queue_type                priority_queues
% 6.60/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.60/1.51  --res_passive_queues_freq               [15;5]
% 6.60/1.51  --res_forward_subs                      full
% 6.60/1.51  --res_backward_subs                     full
% 6.60/1.51  --res_forward_subs_resolution           true
% 6.60/1.51  --res_backward_subs_resolution          true
% 6.60/1.51  --res_orphan_elimination                true
% 6.60/1.51  --res_time_limit                        2.
% 6.60/1.51  --res_out_proof                         true
% 6.60/1.51  
% 6.60/1.51  ------ Superposition Options
% 6.60/1.51  
% 6.60/1.51  --superposition_flag                    true
% 6.60/1.51  --sup_passive_queue_type                priority_queues
% 6.60/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.60/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.60/1.51  --demod_completeness_check              fast
% 6.60/1.51  --demod_use_ground                      true
% 6.60/1.51  --sup_to_prop_solver                    passive
% 6.60/1.51  --sup_prop_simpl_new                    true
% 6.60/1.51  --sup_prop_simpl_given                  true
% 6.60/1.51  --sup_fun_splitting                     false
% 6.60/1.51  --sup_smt_interval                      50000
% 6.60/1.51  
% 6.60/1.51  ------ Superposition Simplification Setup
% 6.60/1.51  
% 6.60/1.51  --sup_indices_passive                   []
% 6.60/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.60/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.60/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.60/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.60/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.60/1.51  --sup_full_bw                           [BwDemod]
% 6.60/1.51  --sup_immed_triv                        [TrivRules]
% 6.60/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.60/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.60/1.51  --sup_immed_bw_main                     []
% 6.60/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.60/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.60/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.60/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.60/1.51  
% 6.60/1.51  ------ Combination Options
% 6.60/1.51  
% 6.60/1.51  --comb_res_mult                         3
% 6.60/1.51  --comb_sup_mult                         2
% 6.60/1.51  --comb_inst_mult                        10
% 6.60/1.51  
% 6.60/1.51  ------ Debug Options
% 6.60/1.51  
% 6.60/1.51  --dbg_backtrace                         false
% 6.60/1.51  --dbg_dump_prop_clauses                 false
% 6.60/1.51  --dbg_dump_prop_clauses_file            -
% 6.60/1.51  --dbg_out_stat                          false
% 6.60/1.51  ------ Parsing...
% 6.60/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.60/1.51  
% 6.60/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 6.60/1.51  
% 6.60/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.60/1.51  
% 6.60/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.60/1.51  ------ Proving...
% 6.60/1.51  ------ Problem Properties 
% 6.60/1.51  
% 6.60/1.51  
% 6.60/1.51  clauses                                 46
% 6.60/1.51  conjectures                             3
% 6.60/1.51  EPR                                     9
% 6.60/1.51  Horn                                    38
% 6.60/1.51  unary                                   7
% 6.60/1.51  binary                                  17
% 6.60/1.51  lits                                    117
% 6.60/1.51  lits eq                                 34
% 6.60/1.51  fd_pure                                 0
% 6.60/1.51  fd_pseudo                               0
% 6.60/1.51  fd_cond                                 2
% 6.60/1.51  fd_pseudo_cond                          2
% 6.60/1.51  AC symbols                              0
% 6.60/1.51  
% 6.60/1.51  ------ Schedule dynamic 5 is on 
% 6.60/1.51  
% 6.60/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.60/1.51  
% 6.60/1.51  
% 6.60/1.51  ------ 
% 6.60/1.51  Current options:
% 6.60/1.51  ------ 
% 6.60/1.51  
% 6.60/1.51  ------ Input Options
% 6.60/1.51  
% 6.60/1.51  --out_options                           all
% 6.60/1.51  --tptp_safe_out                         true
% 6.60/1.51  --problem_path                          ""
% 6.60/1.51  --include_path                          ""
% 6.60/1.51  --clausifier                            res/vclausify_rel
% 6.60/1.51  --clausifier_options                    --mode clausify
% 6.60/1.51  --stdin                                 false
% 6.60/1.51  --stats_out                             all
% 6.60/1.51  
% 6.60/1.51  ------ General Options
% 6.60/1.51  
% 6.60/1.51  --fof                                   false
% 6.60/1.51  --time_out_real                         305.
% 6.60/1.51  --time_out_virtual                      -1.
% 6.60/1.51  --symbol_type_check                     false
% 6.60/1.51  --clausify_out                          false
% 6.60/1.51  --sig_cnt_out                           false
% 6.60/1.51  --trig_cnt_out                          false
% 6.60/1.51  --trig_cnt_out_tolerance                1.
% 6.60/1.51  --trig_cnt_out_sk_spl                   false
% 6.60/1.51  --abstr_cl_out                          false
% 6.60/1.51  
% 6.60/1.51  ------ Global Options
% 6.60/1.51  
% 6.60/1.51  --schedule                              default
% 6.60/1.51  --add_important_lit                     false
% 6.60/1.51  --prop_solver_per_cl                    1000
% 6.60/1.51  --min_unsat_core                        false
% 6.60/1.51  --soft_assumptions                      false
% 6.60/1.51  --soft_lemma_size                       3
% 6.60/1.51  --prop_impl_unit_size                   0
% 6.60/1.51  --prop_impl_unit                        []
% 6.60/1.51  --share_sel_clauses                     true
% 6.60/1.51  --reset_solvers                         false
% 6.60/1.51  --bc_imp_inh                            [conj_cone]
% 6.60/1.51  --conj_cone_tolerance                   3.
% 6.60/1.51  --extra_neg_conj                        none
% 6.60/1.51  --large_theory_mode                     true
% 6.60/1.51  --prolific_symb_bound                   200
% 6.60/1.51  --lt_threshold                          2000
% 6.60/1.51  --clause_weak_htbl                      true
% 6.60/1.51  --gc_record_bc_elim                     false
% 6.60/1.51  
% 6.60/1.51  ------ Preprocessing Options
% 6.60/1.51  
% 6.60/1.51  --preprocessing_flag                    true
% 6.60/1.51  --time_out_prep_mult                    0.1
% 6.60/1.51  --splitting_mode                        input
% 6.60/1.51  --splitting_grd                         true
% 6.60/1.51  --splitting_cvd                         false
% 6.60/1.51  --splitting_cvd_svl                     false
% 6.60/1.51  --splitting_nvd                         32
% 6.60/1.51  --sub_typing                            true
% 6.60/1.51  --prep_gs_sim                           true
% 6.60/1.51  --prep_unflatten                        true
% 6.60/1.51  --prep_res_sim                          true
% 6.60/1.51  --prep_upred                            true
% 6.60/1.51  --prep_sem_filter                       exhaustive
% 6.60/1.51  --prep_sem_filter_out                   false
% 6.60/1.51  --pred_elim                             true
% 6.60/1.51  --res_sim_input                         true
% 6.60/1.51  --eq_ax_congr_red                       true
% 6.60/1.51  --pure_diseq_elim                       true
% 6.60/1.51  --brand_transform                       false
% 6.60/1.51  --non_eq_to_eq                          false
% 6.60/1.51  --prep_def_merge                        true
% 6.60/1.51  --prep_def_merge_prop_impl              false
% 6.60/1.51  --prep_def_merge_mbd                    true
% 6.60/1.51  --prep_def_merge_tr_red                 false
% 6.60/1.51  --prep_def_merge_tr_cl                  false
% 6.60/1.51  --smt_preprocessing                     true
% 6.60/1.51  --smt_ac_axioms                         fast
% 6.60/1.51  --preprocessed_out                      false
% 6.60/1.51  --preprocessed_stats                    false
% 6.60/1.51  
% 6.60/1.51  ------ Abstraction refinement Options
% 6.60/1.51  
% 6.60/1.51  --abstr_ref                             []
% 6.60/1.51  --abstr_ref_prep                        false
% 6.60/1.51  --abstr_ref_until_sat                   false
% 6.60/1.51  --abstr_ref_sig_restrict                funpre
% 6.60/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.60/1.51  --abstr_ref_under                       []
% 6.60/1.51  
% 6.60/1.51  ------ SAT Options
% 6.60/1.51  
% 6.60/1.51  --sat_mode                              false
% 6.60/1.51  --sat_fm_restart_options                ""
% 6.60/1.51  --sat_gr_def                            false
% 6.60/1.51  --sat_epr_types                         true
% 6.60/1.51  --sat_non_cyclic_types                  false
% 6.60/1.51  --sat_finite_models                     false
% 6.60/1.51  --sat_fm_lemmas                         false
% 6.60/1.51  --sat_fm_prep                           false
% 6.60/1.51  --sat_fm_uc_incr                        true
% 6.60/1.51  --sat_out_model                         small
% 6.60/1.51  --sat_out_clauses                       false
% 6.60/1.51  
% 6.60/1.51  ------ QBF Options
% 6.60/1.51  
% 6.60/1.51  --qbf_mode                              false
% 6.60/1.51  --qbf_elim_univ                         false
% 6.60/1.51  --qbf_dom_inst                          none
% 6.60/1.51  --qbf_dom_pre_inst                      false
% 6.60/1.51  --qbf_sk_in                             false
% 6.60/1.51  --qbf_pred_elim                         true
% 6.60/1.51  --qbf_split                             512
% 6.60/1.51  
% 6.60/1.51  ------ BMC1 Options
% 6.60/1.51  
% 6.60/1.51  --bmc1_incremental                      false
% 6.60/1.51  --bmc1_axioms                           reachable_all
% 6.60/1.51  --bmc1_min_bound                        0
% 6.60/1.51  --bmc1_max_bound                        -1
% 6.60/1.51  --bmc1_max_bound_default                -1
% 6.60/1.51  --bmc1_symbol_reachability              true
% 6.60/1.51  --bmc1_property_lemmas                  false
% 6.60/1.51  --bmc1_k_induction                      false
% 6.60/1.51  --bmc1_non_equiv_states                 false
% 6.60/1.51  --bmc1_deadlock                         false
% 6.60/1.51  --bmc1_ucm                              false
% 6.60/1.51  --bmc1_add_unsat_core                   none
% 6.60/1.51  --bmc1_unsat_core_children              false
% 6.60/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.60/1.51  --bmc1_out_stat                         full
% 6.60/1.51  --bmc1_ground_init                      false
% 6.60/1.51  --bmc1_pre_inst_next_state              false
% 6.60/1.51  --bmc1_pre_inst_state                   false
% 6.60/1.51  --bmc1_pre_inst_reach_state             false
% 6.60/1.51  --bmc1_out_unsat_core                   false
% 6.60/1.51  --bmc1_aig_witness_out                  false
% 6.60/1.51  --bmc1_verbose                          false
% 6.60/1.51  --bmc1_dump_clauses_tptp                false
% 6.60/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.60/1.51  --bmc1_dump_file                        -
% 6.60/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.60/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.60/1.51  --bmc1_ucm_extend_mode                  1
% 6.60/1.51  --bmc1_ucm_init_mode                    2
% 6.60/1.51  --bmc1_ucm_cone_mode                    none
% 6.60/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.60/1.51  --bmc1_ucm_relax_model                  4
% 6.60/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.60/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.60/1.51  --bmc1_ucm_layered_model                none
% 6.60/1.51  --bmc1_ucm_max_lemma_size               10
% 6.60/1.51  
% 6.60/1.51  ------ AIG Options
% 6.60/1.51  
% 6.60/1.51  --aig_mode                              false
% 6.60/1.51  
% 6.60/1.51  ------ Instantiation Options
% 6.60/1.51  
% 6.60/1.51  --instantiation_flag                    true
% 6.60/1.51  --inst_sos_flag                         false
% 6.60/1.51  --inst_sos_phase                        true
% 6.60/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.60/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.60/1.51  --inst_lit_sel_side                     none
% 6.60/1.51  --inst_solver_per_active                1400
% 6.60/1.51  --inst_solver_calls_frac                1.
% 6.60/1.51  --inst_passive_queue_type               priority_queues
% 6.60/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.60/1.51  --inst_passive_queues_freq              [25;2]
% 6.60/1.51  --inst_dismatching                      true
% 6.60/1.51  --inst_eager_unprocessed_to_passive     true
% 6.60/1.51  --inst_prop_sim_given                   true
% 6.60/1.51  --inst_prop_sim_new                     false
% 6.60/1.51  --inst_subs_new                         false
% 6.60/1.51  --inst_eq_res_simp                      false
% 6.60/1.51  --inst_subs_given                       false
% 6.60/1.51  --inst_orphan_elimination               true
% 6.60/1.51  --inst_learning_loop_flag               true
% 6.60/1.51  --inst_learning_start                   3000
% 6.60/1.51  --inst_learning_factor                  2
% 6.60/1.51  --inst_start_prop_sim_after_learn       3
% 6.60/1.51  --inst_sel_renew                        solver
% 6.60/1.51  --inst_lit_activity_flag                true
% 6.60/1.51  --inst_restr_to_given                   false
% 6.60/1.51  --inst_activity_threshold               500
% 6.60/1.51  --inst_out_proof                        true
% 6.60/1.51  
% 6.60/1.51  ------ Resolution Options
% 6.60/1.51  
% 6.60/1.51  --resolution_flag                       false
% 6.60/1.51  --res_lit_sel                           adaptive
% 6.60/1.51  --res_lit_sel_side                      none
% 6.60/1.51  --res_ordering                          kbo
% 6.60/1.51  --res_to_prop_solver                    active
% 6.60/1.51  --res_prop_simpl_new                    false
% 6.60/1.51  --res_prop_simpl_given                  true
% 6.60/1.51  --res_passive_queue_type                priority_queues
% 6.60/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.60/1.51  --res_passive_queues_freq               [15;5]
% 6.60/1.51  --res_forward_subs                      full
% 6.60/1.51  --res_backward_subs                     full
% 6.60/1.51  --res_forward_subs_resolution           true
% 6.60/1.51  --res_backward_subs_resolution          true
% 6.60/1.51  --res_orphan_elimination                true
% 6.60/1.51  --res_time_limit                        2.
% 6.60/1.51  --res_out_proof                         true
% 6.60/1.51  
% 6.60/1.51  ------ Superposition Options
% 6.60/1.51  
% 6.60/1.51  --superposition_flag                    true
% 6.60/1.51  --sup_passive_queue_type                priority_queues
% 6.60/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.60/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.60/1.51  --demod_completeness_check              fast
% 6.60/1.51  --demod_use_ground                      true
% 6.60/1.51  --sup_to_prop_solver                    passive
% 6.60/1.51  --sup_prop_simpl_new                    true
% 6.60/1.51  --sup_prop_simpl_given                  true
% 6.60/1.51  --sup_fun_splitting                     false
% 6.60/1.51  --sup_smt_interval                      50000
% 6.60/1.51  
% 6.60/1.51  ------ Superposition Simplification Setup
% 6.60/1.51  
% 6.60/1.51  --sup_indices_passive                   []
% 6.60/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.60/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.60/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.60/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.60/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.60/1.51  --sup_full_bw                           [BwDemod]
% 6.60/1.51  --sup_immed_triv                        [TrivRules]
% 6.60/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.60/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.60/1.51  --sup_immed_bw_main                     []
% 6.60/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.60/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.60/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.60/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.60/1.51  
% 6.60/1.51  ------ Combination Options
% 6.60/1.51  
% 6.60/1.51  --comb_res_mult                         3
% 6.60/1.51  --comb_sup_mult                         2
% 6.60/1.51  --comb_inst_mult                        10
% 6.60/1.51  
% 6.60/1.51  ------ Debug Options
% 6.60/1.51  
% 6.60/1.51  --dbg_backtrace                         false
% 6.60/1.51  --dbg_dump_prop_clauses                 false
% 6.60/1.51  --dbg_dump_prop_clauses_file            -
% 6.60/1.51  --dbg_out_stat                          false
% 6.60/1.51  
% 6.60/1.51  
% 6.60/1.51  
% 6.60/1.51  
% 6.60/1.51  ------ Proving...
% 6.60/1.51  
% 6.60/1.51  
% 6.60/1.51  % SZS status Theorem for theBenchmark.p
% 6.60/1.51  
% 6.60/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 6.60/1.51  
% 6.60/1.51  fof(f6,axiom,(
% 6.60/1.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f97,plain,(
% 6.60/1.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 6.60/1.51    inference(cnf_transformation,[],[f6])).
% 6.60/1.51  
% 6.60/1.51  fof(f17,axiom,(
% 6.60/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f48,plain,(
% 6.60/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.60/1.51    inference(ennf_transformation,[],[f17])).
% 6.60/1.51  
% 6.60/1.51  fof(f110,plain,(
% 6.60/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.60/1.51    inference(cnf_transformation,[],[f48])).
% 6.60/1.51  
% 6.60/1.51  fof(f8,axiom,(
% 6.60/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f78,plain,(
% 6.60/1.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.60/1.51    inference(nnf_transformation,[],[f8])).
% 6.60/1.51  
% 6.60/1.51  fof(f99,plain,(
% 6.60/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.60/1.51    inference(cnf_transformation,[],[f78])).
% 6.60/1.51  
% 6.60/1.51  fof(f13,axiom,(
% 6.60/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f42,plain,(
% 6.60/1.51    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 6.60/1.51    inference(ennf_transformation,[],[f13])).
% 6.60/1.51  
% 6.60/1.51  fof(f43,plain,(
% 6.60/1.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 6.60/1.51    inference(flattening,[],[f42])).
% 6.60/1.51  
% 6.60/1.51  fof(f105,plain,(
% 6.60/1.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f43])).
% 6.60/1.51  
% 6.60/1.51  fof(f18,axiom,(
% 6.60/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f31,plain,(
% 6.60/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 6.60/1.51    inference(pure_predicate_removal,[],[f18])).
% 6.60/1.51  
% 6.60/1.51  fof(f49,plain,(
% 6.60/1.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.60/1.51    inference(ennf_transformation,[],[f31])).
% 6.60/1.51  
% 6.60/1.51  fof(f111,plain,(
% 6.60/1.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.60/1.51    inference(cnf_transformation,[],[f49])).
% 6.60/1.51  
% 6.60/1.51  fof(f11,axiom,(
% 6.60/1.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f39,plain,(
% 6.60/1.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.60/1.51    inference(ennf_transformation,[],[f11])).
% 6.60/1.51  
% 6.60/1.51  fof(f40,plain,(
% 6.60/1.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.60/1.51    inference(flattening,[],[f39])).
% 6.60/1.51  
% 6.60/1.51  fof(f103,plain,(
% 6.60/1.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f40])).
% 6.60/1.51  
% 6.60/1.51  fof(f2,axiom,(
% 6.60/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f32,plain,(
% 6.60/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.60/1.51    inference(ennf_transformation,[],[f2])).
% 6.60/1.51  
% 6.60/1.51  fof(f70,plain,(
% 6.60/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.60/1.51    inference(nnf_transformation,[],[f32])).
% 6.60/1.51  
% 6.60/1.51  fof(f71,plain,(
% 6.60/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.60/1.51    inference(rectify,[],[f70])).
% 6.60/1.51  
% 6.60/1.51  fof(f72,plain,(
% 6.60/1.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 6.60/1.51    introduced(choice_axiom,[])).
% 6.60/1.51  
% 6.60/1.51  fof(f73,plain,(
% 6.60/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.60/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f71,f72])).
% 6.60/1.51  
% 6.60/1.51  fof(f88,plain,(
% 6.60/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f73])).
% 6.60/1.51  
% 6.60/1.51  fof(f1,axiom,(
% 6.60/1.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f66,plain,(
% 6.60/1.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 6.60/1.51    inference(nnf_transformation,[],[f1])).
% 6.60/1.51  
% 6.60/1.51  fof(f67,plain,(
% 6.60/1.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.60/1.51    inference(rectify,[],[f66])).
% 6.60/1.51  
% 6.60/1.51  fof(f68,plain,(
% 6.60/1.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 6.60/1.51    introduced(choice_axiom,[])).
% 6.60/1.51  
% 6.60/1.51  fof(f69,plain,(
% 6.60/1.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.60/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f67,f68])).
% 6.60/1.51  
% 6.60/1.51  fof(f85,plain,(
% 6.60/1.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f69])).
% 6.60/1.51  
% 6.60/1.51  fof(f28,conjecture,(
% 6.60/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)))) & v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)) & v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))))))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f29,negated_conjecture,(
% 6.60/1.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)))) & v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)) & v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))))))),
% 6.60/1.51    inference(negated_conjecture,[],[f28])).
% 6.60/1.51  
% 6.60/1.51  fof(f30,plain,(
% 6.60/1.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)))) & v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)) & v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))))))),
% 6.60/1.51    inference(pure_predicate_removal,[],[f29])).
% 6.60/1.51  
% 6.60/1.51  fof(f64,plain,(
% 6.60/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)) | ~v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 6.60/1.51    inference(ennf_transformation,[],[f30])).
% 6.60/1.51  
% 6.60/1.51  fof(f65,plain,(
% 6.60/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)) | ~v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 6.60/1.51    inference(flattening,[],[f64])).
% 6.60/1.51  
% 6.60/1.51  fof(f83,plain,(
% 6.60/1.51    ( ! [X2,X0,X1] : (? [X3] : ((~m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)) | ~v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => ((~m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,sK5)),u1_struct_0(X1)))) | ~v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5),u1_struct_0(k1_pre_topc(X0,sK5)),u1_struct_0(X1)) | ~v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 6.60/1.51    introduced(choice_axiom,[])).
% 6.60/1.51  
% 6.60/1.51  fof(f82,plain,(
% 6.60/1.51    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)) | ~v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)) | ~v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 6.60/1.51    introduced(choice_axiom,[])).
% 6.60/1.51  
% 6.60/1.51  fof(f81,plain,(
% 6.60/1.51    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)) | ~v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((~m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(sK3)))) | ~v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(sK3)) | ~v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3))) )),
% 6.60/1.51    introduced(choice_axiom,[])).
% 6.60/1.51  
% 6.60/1.51  fof(f80,plain,(
% 6.60/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1)) | ~v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k5_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(sK2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1)) & l1_pre_topc(sK2))),
% 6.60/1.51    introduced(choice_axiom,[])).
% 6.60/1.51  
% 6.60/1.51  fof(f84,plain,(
% 6.60/1.51    ((((~m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3)) & l1_pre_topc(sK2)),
% 6.60/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f65,f83,f82,f81,f80])).
% 6.60/1.51  
% 6.60/1.51  fof(f136,plain,(
% 6.60/1.51    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 6.60/1.51    inference(cnf_transformation,[],[f84])).
% 6.60/1.51  
% 6.60/1.51  fof(f3,axiom,(
% 6.60/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f74,plain,(
% 6.60/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.60/1.51    inference(nnf_transformation,[],[f3])).
% 6.60/1.51  
% 6.60/1.51  fof(f75,plain,(
% 6.60/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.60/1.51    inference(flattening,[],[f74])).
% 6.60/1.51  
% 6.60/1.51  fof(f92,plain,(
% 6.60/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f75])).
% 6.60/1.51  
% 6.60/1.51  fof(f135,plain,(
% 6.60/1.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 6.60/1.51    inference(cnf_transformation,[],[f84])).
% 6.60/1.51  
% 6.60/1.51  fof(f19,axiom,(
% 6.60/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f50,plain,(
% 6.60/1.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.60/1.51    inference(ennf_transformation,[],[f19])).
% 6.60/1.51  
% 6.60/1.51  fof(f112,plain,(
% 6.60/1.51    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.60/1.51    inference(cnf_transformation,[],[f50])).
% 6.60/1.51  
% 6.60/1.51  fof(f23,axiom,(
% 6.60/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f55,plain,(
% 6.60/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.60/1.51    inference(ennf_transformation,[],[f23])).
% 6.60/1.51  
% 6.60/1.51  fof(f56,plain,(
% 6.60/1.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.60/1.51    inference(flattening,[],[f55])).
% 6.60/1.51  
% 6.60/1.51  fof(f79,plain,(
% 6.60/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.60/1.51    inference(nnf_transformation,[],[f56])).
% 6.60/1.51  
% 6.60/1.51  fof(f118,plain,(
% 6.60/1.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.60/1.51    inference(cnf_transformation,[],[f79])).
% 6.60/1.51  
% 6.60/1.51  fof(f134,plain,(
% 6.60/1.51    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 6.60/1.51    inference(cnf_transformation,[],[f84])).
% 6.60/1.51  
% 6.60/1.51  fof(f122,plain,(
% 6.60/1.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.60/1.51    inference(cnf_transformation,[],[f79])).
% 6.60/1.51  
% 6.60/1.51  fof(f144,plain,(
% 6.60/1.51    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 6.60/1.51    inference(equality_resolution,[],[f122])).
% 6.60/1.51  
% 6.60/1.51  fof(f5,axiom,(
% 6.60/1.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f76,plain,(
% 6.60/1.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.60/1.51    inference(nnf_transformation,[],[f5])).
% 6.60/1.51  
% 6.60/1.51  fof(f77,plain,(
% 6.60/1.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.60/1.51    inference(flattening,[],[f76])).
% 6.60/1.51  
% 6.60/1.51  fof(f96,plain,(
% 6.60/1.51    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 6.60/1.51    inference(cnf_transformation,[],[f77])).
% 6.60/1.51  
% 6.60/1.51  fof(f140,plain,(
% 6.60/1.51    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 6.60/1.51    inference(equality_resolution,[],[f96])).
% 6.60/1.51  
% 6.60/1.51  fof(f86,plain,(
% 6.60/1.51    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f69])).
% 6.60/1.51  
% 6.60/1.51  fof(f16,axiom,(
% 6.60/1.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f47,plain,(
% 6.60/1.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 6.60/1.51    inference(ennf_transformation,[],[f16])).
% 6.60/1.51  
% 6.60/1.51  fof(f109,plain,(
% 6.60/1.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f47])).
% 6.60/1.51  
% 6.60/1.51  fof(f4,axiom,(
% 6.60/1.51    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f33,plain,(
% 6.60/1.51    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 6.60/1.51    inference(ennf_transformation,[],[f4])).
% 6.60/1.51  
% 6.60/1.51  fof(f93,plain,(
% 6.60/1.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f33])).
% 6.60/1.51  
% 6.60/1.51  fof(f87,plain,(
% 6.60/1.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f73])).
% 6.60/1.51  
% 6.60/1.51  fof(f25,axiom,(
% 6.60/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f59,plain,(
% 6.60/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.60/1.51    inference(ennf_transformation,[],[f25])).
% 6.60/1.51  
% 6.60/1.51  fof(f60,plain,(
% 6.60/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.60/1.51    inference(flattening,[],[f59])).
% 6.60/1.51  
% 6.60/1.51  fof(f126,plain,(
% 6.60/1.51    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f60])).
% 6.60/1.51  
% 6.60/1.51  fof(f133,plain,(
% 6.60/1.51    v1_funct_1(sK4)),
% 6.60/1.51    inference(cnf_transformation,[],[f84])).
% 6.60/1.51  
% 6.60/1.51  fof(f24,axiom,(
% 6.60/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f57,plain,(
% 6.60/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.60/1.51    inference(ennf_transformation,[],[f24])).
% 6.60/1.51  
% 6.60/1.51  fof(f58,plain,(
% 6.60/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.60/1.51    inference(flattening,[],[f57])).
% 6.60/1.51  
% 6.60/1.51  fof(f125,plain,(
% 6.60/1.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f58])).
% 6.60/1.51  
% 6.60/1.51  fof(f20,axiom,(
% 6.60/1.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f51,plain,(
% 6.60/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.60/1.51    inference(ennf_transformation,[],[f20])).
% 6.60/1.51  
% 6.60/1.51  fof(f113,plain,(
% 6.60/1.51    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.60/1.51    inference(cnf_transformation,[],[f51])).
% 6.60/1.51  
% 6.60/1.51  fof(f21,axiom,(
% 6.60/1.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f52,plain,(
% 6.60/1.51    ! [X0,X1,X2,X3] : (m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 6.60/1.51    inference(ennf_transformation,[],[f21])).
% 6.60/1.51  
% 6.60/1.51  fof(f114,plain,(
% 6.60/1.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 6.60/1.51    inference(cnf_transformation,[],[f52])).
% 6.60/1.51  
% 6.60/1.51  fof(f26,axiom,(
% 6.60/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f61,plain,(
% 6.60/1.51    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.60/1.51    inference(ennf_transformation,[],[f26])).
% 6.60/1.51  
% 6.60/1.51  fof(f62,plain,(
% 6.60/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.60/1.51    inference(flattening,[],[f61])).
% 6.60/1.51  
% 6.60/1.51  fof(f128,plain,(
% 6.60/1.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f62])).
% 6.60/1.51  
% 6.60/1.51  fof(f137,plain,(
% 6.60/1.51    ~m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))),
% 6.60/1.51    inference(cnf_transformation,[],[f84])).
% 6.60/1.51  
% 6.60/1.51  fof(f27,axiom,(
% 6.60/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f63,plain,(
% 6.60/1.51    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.60/1.51    inference(ennf_transformation,[],[f27])).
% 6.60/1.51  
% 6.60/1.51  fof(f130,plain,(
% 6.60/1.51    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f63])).
% 6.60/1.51  
% 6.60/1.51  fof(f131,plain,(
% 6.60/1.51    l1_pre_topc(sK2)),
% 6.60/1.51    inference(cnf_transformation,[],[f84])).
% 6.60/1.51  
% 6.60/1.51  fof(f15,axiom,(
% 6.60/1.51    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f45,plain,(
% 6.60/1.51    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.60/1.51    inference(ennf_transformation,[],[f15])).
% 6.60/1.51  
% 6.60/1.51  fof(f46,plain,(
% 6.60/1.51    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.60/1.51    inference(flattening,[],[f45])).
% 6.60/1.51  
% 6.60/1.51  fof(f108,plain,(
% 6.60/1.51    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f46])).
% 6.60/1.51  
% 6.60/1.51  fof(f121,plain,(
% 6.60/1.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.60/1.51    inference(cnf_transformation,[],[f79])).
% 6.60/1.51  
% 6.60/1.51  fof(f145,plain,(
% 6.60/1.51    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 6.60/1.51    inference(equality_resolution,[],[f121])).
% 6.60/1.51  
% 6.60/1.51  fof(f95,plain,(
% 6.60/1.51    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 6.60/1.51    inference(cnf_transformation,[],[f77])).
% 6.60/1.51  
% 6.60/1.51  fof(f141,plain,(
% 6.60/1.51    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 6.60/1.51    inference(equality_resolution,[],[f95])).
% 6.60/1.51  
% 6.60/1.51  fof(f123,plain,(
% 6.60/1.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.60/1.51    inference(cnf_transformation,[],[f79])).
% 6.60/1.51  
% 6.60/1.51  fof(f142,plain,(
% 6.60/1.51    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.60/1.51    inference(equality_resolution,[],[f123])).
% 6.60/1.51  
% 6.60/1.51  fof(f143,plain,(
% 6.60/1.51    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 6.60/1.51    inference(equality_resolution,[],[f142])).
% 6.60/1.51  
% 6.60/1.51  fof(f22,axiom,(
% 6.60/1.51    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f53,plain,(
% 6.60/1.51    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 6.60/1.51    inference(ennf_transformation,[],[f22])).
% 6.60/1.51  
% 6.60/1.51  fof(f54,plain,(
% 6.60/1.51    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.60/1.51    inference(flattening,[],[f53])).
% 6.60/1.51  
% 6.60/1.51  fof(f116,plain,(
% 6.60/1.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f54])).
% 6.60/1.51  
% 6.60/1.51  fof(f14,axiom,(
% 6.60/1.51    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 6.60/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.60/1.51  
% 6.60/1.51  fof(f44,plain,(
% 6.60/1.51    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 6.60/1.51    inference(ennf_transformation,[],[f14])).
% 6.60/1.51  
% 6.60/1.51  fof(f106,plain,(
% 6.60/1.51    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 6.60/1.51    inference(cnf_transformation,[],[f44])).
% 6.60/1.51  
% 6.60/1.51  cnf(c_12,plain,
% 6.60/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 6.60/1.51      inference(cnf_transformation,[],[f97]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2269,plain,
% 6.60/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_25,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | v1_relat_1(X0) ),
% 6.60/1.51      inference(cnf_transformation,[],[f110]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2258,plain,
% 6.60/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.60/1.51      | v1_relat_1(X0) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3573,plain,
% 6.60/1.51      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_2269,c_2258]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_15,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.60/1.51      inference(cnf_transformation,[],[f99]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2267,plain,
% 6.60/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.60/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3396,plain,
% 6.60/1.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_2269,c_2267]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_20,plain,
% 6.60/1.51      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 6.60/1.51      | ~ v1_relat_1(X1)
% 6.60/1.51      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 6.60/1.51      inference(cnf_transformation,[],[f105]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2263,plain,
% 6.60/1.51      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 6.60/1.51      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 6.60/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_12522,plain,
% 6.60/1.51      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 6.60/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_3396,c_2263]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_19722,plain,
% 6.60/1.51      ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_3573,c_12522]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_26,plain,
% 6.60/1.51      ( v4_relat_1(X0,X1)
% 6.60/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.60/1.51      inference(cnf_transformation,[],[f111]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_18,plain,
% 6.60/1.51      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 6.60/1.51      inference(cnf_transformation,[],[f103]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_616,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | ~ v1_relat_1(X0)
% 6.60/1.51      | k7_relat_1(X0,X1) = X0 ),
% 6.60/1.51      inference(resolution,[status(thm)],[c_26,c_18]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_620,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | k7_relat_1(X0,X1) = X0 ),
% 6.60/1.51      inference(global_propositional_subsumption,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_616,c_26,c_25,c_18]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2247,plain,
% 6.60/1.51      ( k7_relat_1(X0,X1) = X0
% 6.60/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3508,plain,
% 6.60/1.51      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_2269,c_2247]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_19727,plain,
% 6.60/1.51      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_19722,c_3508]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3,plain,
% 6.60/1.51      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 6.60/1.51      inference(cnf_transformation,[],[f88]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2274,plain,
% 6.60/1.51      ( r1_tarski(X0,X1) = iProver_top
% 6.60/1.51      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_1,plain,
% 6.60/1.51      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 6.60/1.51      inference(cnf_transformation,[],[f85]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2276,plain,
% 6.60/1.51      ( r2_hidden(X0,X1) != iProver_top
% 6.60/1.51      | v1_xboole_0(X1) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3555,plain,
% 6.60/1.51      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_2274,c_2276]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_47,negated_conjecture,
% 6.60/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 6.60/1.51      inference(cnf_transformation,[],[f136]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2251,plain,
% 6.60/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3397,plain,
% 6.60/1.51      ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_2251,c_2267]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_5,plain,
% 6.60/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 6.60/1.51      inference(cnf_transformation,[],[f92]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2272,plain,
% 6.60/1.51      ( X0 = X1
% 6.60/1.51      | r1_tarski(X1,X0) != iProver_top
% 6.60/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_5394,plain,
% 6.60/1.51      ( u1_struct_0(sK2) = sK5
% 6.60/1.51      | r1_tarski(u1_struct_0(sK2),sK5) != iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_3397,c_2272]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_18274,plain,
% 6.60/1.51      ( u1_struct_0(sK2) = sK5
% 6.60/1.51      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_3555,c_5394]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_48,negated_conjecture,
% 6.60/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 6.60/1.51      inference(cnf_transformation,[],[f135]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2250,plain,
% 6.60/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_27,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 6.60/1.51      inference(cnf_transformation,[],[f112]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2257,plain,
% 6.60/1.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 6.60/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_4058,plain,
% 6.60/1.51      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k1_relat_1(sK4) ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_2250,c_2257]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_38,plain,
% 6.60/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 6.60/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | k1_relset_1(X1,X2,X0) = X1
% 6.60/1.51      | k1_xboole_0 = X2 ),
% 6.60/1.51      inference(cnf_transformation,[],[f118]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_49,negated_conjecture,
% 6.60/1.51      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 6.60/1.51      inference(cnf_transformation,[],[f134]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_760,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | k1_relset_1(X1,X2,X0) = X1
% 6.60/1.51      | u1_struct_0(sK3) != X2
% 6.60/1.51      | u1_struct_0(sK2) != X1
% 6.60/1.51      | sK4 != X0
% 6.60/1.51      | k1_xboole_0 = X2 ),
% 6.60/1.51      inference(resolution_lifted,[status(thm)],[c_38,c_49]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_761,plain,
% 6.60/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 6.60/1.51      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = u1_struct_0(sK2)
% 6.60/1.51      | k1_xboole_0 = u1_struct_0(sK3) ),
% 6.60/1.51      inference(unflattening,[status(thm)],[c_760]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_763,plain,
% 6.60/1.51      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = u1_struct_0(sK2)
% 6.60/1.51      | k1_xboole_0 = u1_struct_0(sK3) ),
% 6.60/1.51      inference(global_propositional_subsumption,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_761,c_48]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_4153,plain,
% 6.60/1.51      ( u1_struct_0(sK3) = k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK2) = k1_relat_1(sK4) ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_4058,c_763]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_34,plain,
% 6.60/1.51      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 6.60/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 6.60/1.51      | k1_xboole_0 = X1
% 6.60/1.51      | k1_xboole_0 = X0 ),
% 6.60/1.51      inference(cnf_transformation,[],[f144]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_799,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 6.60/1.51      | u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK2) != X1
% 6.60/1.51      | sK4 != X0
% 6.60/1.51      | k1_xboole_0 = X0
% 6.60/1.51      | k1_xboole_0 = X1 ),
% 6.60/1.51      inference(resolution_lifted,[status(thm)],[c_34,c_49]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_800,plain,
% 6.60/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 6.60/1.51      | u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | k1_xboole_0 = u1_struct_0(sK2)
% 6.60/1.51      | k1_xboole_0 = sK4 ),
% 6.60/1.51      inference(unflattening,[status(thm)],[c_799]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2239,plain,
% 6.60/1.51      ( u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | k1_xboole_0 = u1_struct_0(sK2)
% 6.60/1.51      | k1_xboole_0 = sK4
% 6.60/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_9,plain,
% 6.60/1.51      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.60/1.51      inference(cnf_transformation,[],[f140]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2439,plain,
% 6.60/1.51      ( u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK2) = k1_xboole_0
% 6.60/1.51      | sK4 = k1_xboole_0
% 6.60/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_2239,c_9]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_4247,plain,
% 6.60/1.51      ( u1_struct_0(sK2) = k1_relat_1(sK4)
% 6.60/1.51      | u1_struct_0(sK2) = k1_xboole_0
% 6.60/1.51      | sK4 = k1_xboole_0
% 6.60/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_4153,c_2439]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_4256,plain,
% 6.60/1.51      ( u1_struct_0(sK2) = k1_relat_1(sK4)
% 6.60/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_4153,c_2250]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_4259,plain,
% 6.60/1.51      ( u1_struct_0(sK2) = k1_relat_1(sK4)
% 6.60/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_4256,c_9]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_4322,plain,
% 6.60/1.51      ( u1_struct_0(sK2) = k1_relat_1(sK4)
% 6.60/1.51      | u1_struct_0(sK2) = k1_xboole_0
% 6.60/1.51      | sK4 = k1_xboole_0 ),
% 6.60/1.51      inference(forward_subsumption_resolution,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_4247,c_4259]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_0,plain,
% 6.60/1.51      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 6.60/1.51      inference(cnf_transformation,[],[f86]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_168,plain,
% 6.60/1.51      ( r2_hidden(sK0(X0),X0) = iProver_top
% 6.60/1.51      | v1_xboole_0(X0) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_170,plain,
% 6.60/1.51      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top
% 6.60/1.51      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_168]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_24,plain,
% 6.60/1.51      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 6.60/1.51      inference(cnf_transformation,[],[f109]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2907,plain,
% 6.60/1.51      ( ~ r1_tarski(X0,sK0(X0)) | ~ r2_hidden(sK0(X0),X0) ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_24]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2908,plain,
% 6.60/1.51      ( r1_tarski(X0,sK0(X0)) != iProver_top
% 6.60/1.51      | r2_hidden(sK0(X0),X0) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_2907]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2910,plain,
% 6.60/1.51      ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) != iProver_top
% 6.60/1.51      | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_2908]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3328,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0(X0))) | r1_tarski(X0,sK0(X0)) ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3329,plain,
% 6.60/1.51      ( m1_subset_1(X0,k1_zfmisc_1(sK0(X0))) != iProver_top
% 6.60/1.51      | r1_tarski(X0,sK0(X0)) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_3328]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3331,plain,
% 6.60/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(k1_xboole_0))) != iProver_top
% 6.60/1.51      | r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) = iProver_top ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_3329]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_8,plain,
% 6.60/1.51      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 6.60/1.51      inference(cnf_transformation,[],[f93]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6548,plain,
% 6.60/1.51      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK4) | sK4 = X0 ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_8]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6549,plain,
% 6.60/1.51      ( sK4 = X0
% 6.60/1.51      | v1_xboole_0(X0) != iProver_top
% 6.60/1.51      | v1_xboole_0(sK4) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_6548]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6551,plain,
% 6.60/1.51      ( sK4 = k1_xboole_0
% 6.60/1.51      | v1_xboole_0(sK4) != iProver_top
% 6.60/1.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_6549]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_7412,plain,
% 6.60/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(k1_xboole_0))) ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_12]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_7415,plain,
% 6.60/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(k1_xboole_0))) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_7412]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2277,plain,
% 6.60/1.51      ( r2_hidden(sK0(X0),X0) = iProver_top
% 6.60/1.51      | v1_xboole_0(X0) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3398,plain,
% 6.60/1.51      ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_2250,c_2267]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_4,plain,
% 6.60/1.51      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 6.60/1.51      inference(cnf_transformation,[],[f87]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2273,plain,
% 6.60/1.51      ( r1_tarski(X0,X1) != iProver_top
% 6.60/1.51      | r2_hidden(X2,X0) != iProver_top
% 6.60/1.51      | r2_hidden(X2,X1) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_7697,plain,
% 6.60/1.51      ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top
% 6.60/1.51      | r2_hidden(X0,sK4) != iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_3398,c_2273]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_7899,plain,
% 6.60/1.51      ( r2_hidden(X0,sK4) != iProver_top
% 6.60/1.51      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_7697,c_2276]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_11045,plain,
% 6.60/1.51      ( u1_struct_0(sK2) = k1_relat_1(sK4)
% 6.60/1.51      | r2_hidden(X0,sK4) != iProver_top
% 6.60/1.51      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_4153,c_7899]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_11046,plain,
% 6.60/1.51      ( u1_struct_0(sK2) = k1_relat_1(sK4)
% 6.60/1.51      | r2_hidden(X0,sK4) != iProver_top
% 6.60/1.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_11045,c_9]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_11292,plain,
% 6.60/1.51      ( r2_hidden(X0,sK4) != iProver_top
% 6.60/1.51      | u1_struct_0(sK2) = k1_relat_1(sK4) ),
% 6.60/1.51      inference(global_propositional_subsumption,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_11046,c_170,c_2910,c_3331,c_7415]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_11293,plain,
% 6.60/1.51      ( u1_struct_0(sK2) = k1_relat_1(sK4)
% 6.60/1.51      | r2_hidden(X0,sK4) != iProver_top ),
% 6.60/1.51      inference(renaming,[status(thm)],[c_11292]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_11298,plain,
% 6.60/1.51      ( u1_struct_0(sK2) = k1_relat_1(sK4)
% 6.60/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_2277,c_11293]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_15269,plain,
% 6.60/1.51      ( u1_struct_0(sK2) = k1_relat_1(sK4) | sK4 = k1_xboole_0 ),
% 6.60/1.51      inference(global_propositional_subsumption,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_4322,c_170,c_2910,c_3331,c_6551,c_7415,c_11298]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3509,plain,
% 6.60/1.51      ( k7_relat_1(sK4,u1_struct_0(sK2)) = sK4 ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_2250,c_2247]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_15318,plain,
% 6.60/1.51      ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 | sK4 = k1_xboole_0 ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_15269,c_3509]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_41,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | ~ v1_funct_1(X0)
% 6.60/1.51      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 6.60/1.51      inference(cnf_transformation,[],[f126]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2252,plain,
% 6.60/1.51      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 6.60/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.60/1.51      | v1_funct_1(X2) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3915,plain,
% 6.60/1.51      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0)
% 6.60/1.51      | v1_funct_1(sK4) != iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_2250,c_2252]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_50,negated_conjecture,
% 6.60/1.51      ( v1_funct_1(sK4) ),
% 6.60/1.51      inference(cnf_transformation,[],[f133]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2719,plain,
% 6.60/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 6.60/1.51      | ~ v1_funct_1(sK4)
% 6.60/1.51      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0) ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_41]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_4156,plain,
% 6.60/1.51      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0) ),
% 6.60/1.51      inference(global_propositional_subsumption,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_3915,c_50,c_48,c_2719]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_39,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | ~ v1_funct_1(X0) ),
% 6.60/1.51      inference(cnf_transformation,[],[f125]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2254,plain,
% 6.60/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.60/1.51      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 6.60/1.51      | v1_funct_1(X0) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_5281,plain,
% 6.60/1.51      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
% 6.60/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | v1_funct_1(sK4) != iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_4156,c_2254]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_55,plain,
% 6.60/1.51      ( v1_funct_1(sK4) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_57,plain,
% 6.60/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6070,plain,
% 6.60/1.51      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 6.60/1.51      inference(global_propositional_subsumption,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_5281,c_55,c_57]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6084,plain,
% 6.60/1.51      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_6070,c_2257]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_15702,plain,
% 6.60/1.51      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k1_relat_1(k7_relat_1(sK4,k1_relat_1(sK4)))
% 6.60/1.51      | sK4 = k1_xboole_0 ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_15318,c_6084]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_15723,plain,
% 6.60/1.51      ( k1_relat_1(k7_relat_1(sK4,k1_relat_1(sK4))) = k1_relat_1(sK4)
% 6.60/1.51      | sK4 = k1_xboole_0 ),
% 6.60/1.51      inference(light_normalisation,[status(thm)],[c_15702,c_4058]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2649,plain,
% 6.60/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 6.60/1.51      | v1_relat_1(sK4) ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_25]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2650,plain,
% 6.60/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | v1_relat_1(sK4) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_2649]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_28,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 6.60/1.51      inference(cnf_transformation,[],[f113]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2256,plain,
% 6.60/1.51      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 6.60/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_5619,plain,
% 6.60/1.51      ( k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k7_relat_1(sK4,X0) ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_2250,c_2256]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_29,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | m1_subset_1(k5_relset_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
% 6.60/1.51      inference(cnf_transformation,[],[f114]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2255,plain,
% 6.60/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.60/1.51      | m1_subset_1(k5_relset_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6186,plain,
% 6.60/1.51      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK3)))) = iProver_top
% 6.60/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_5619,c_2255]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6659,plain,
% 6.60/1.51      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK3)))) = iProver_top ),
% 6.60/1.51      inference(global_propositional_subsumption,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_6186,c_57]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6674,plain,
% 6.60/1.51      ( k1_relset_1(X0,u1_struct_0(sK3),k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_6659,c_2257]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_43,plain,
% 6.60/1.51      ( v1_funct_2(X0,X1,X2)
% 6.60/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | ~ v1_funct_1(X0)
% 6.60/1.51      | k1_relset_1(X1,X2,X0) != X1 ),
% 6.60/1.51      inference(cnf_transformation,[],[f128]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_46,negated_conjecture,
% 6.60/1.51      ( ~ v1_funct_2(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))
% 6.60/1.51      | ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
% 6.60/1.51      | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
% 6.60/1.51      inference(cnf_transformation,[],[f137]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_728,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
% 6.60/1.51      | ~ v1_funct_1(X0)
% 6.60/1.51      | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 6.60/1.51      | k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != X0
% 6.60/1.51      | k1_relset_1(X1,X2,X0) != X1
% 6.60/1.51      | u1_struct_0(k1_pre_topc(sK2,sK5)) != X1
% 6.60/1.51      | u1_struct_0(sK3) != X2 ),
% 6.60/1.51      inference(resolution_lifted,[status(thm)],[c_43,c_46]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_729,plain,
% 6.60/1.51      ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
% 6.60/1.51      | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 6.60/1.51      | k1_relset_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3),k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != u1_struct_0(k1_pre_topc(sK2,sK5)) ),
% 6.60/1.51      inference(unflattening,[status(thm)],[c_728]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2242,plain,
% 6.60/1.51      ( k1_relset_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3),k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != u1_struct_0(k1_pre_topc(sK2,sK5))
% 6.60/1.51      | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_45,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.60/1.51      | ~ l1_pre_topc(X1)
% 6.60/1.51      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 6.60/1.51      inference(cnf_transformation,[],[f130]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_52,negated_conjecture,
% 6.60/1.51      ( l1_pre_topc(sK2) ),
% 6.60/1.51      inference(cnf_transformation,[],[f131]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_648,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.60/1.51      | u1_struct_0(k1_pre_topc(X1,X0)) = X0
% 6.60/1.51      | sK2 != X1 ),
% 6.60/1.51      inference(resolution_lifted,[status(thm)],[c_45,c_52]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_649,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 6.60/1.51      | u1_struct_0(k1_pre_topc(sK2,X0)) = X0 ),
% 6.60/1.51      inference(unflattening,[status(thm)],[c_648]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2245,plain,
% 6.60/1.51      ( u1_struct_0(k1_pre_topc(sK2,X0)) = X0
% 6.60/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2666,plain,
% 6.60/1.51      ( u1_struct_0(k1_pre_topc(sK2,sK5)) = sK5 ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_2251,c_2245]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2728,plain,
% 6.60/1.51      ( k1_relset_1(sK5,u1_struct_0(sK3),k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != sK5
% 6.60/1.51      | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
% 6.60/1.51      inference(light_normalisation,[status(thm)],[c_2242,c_2666]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_5659,plain,
% 6.60/1.51      ( k1_relset_1(sK5,u1_struct_0(sK3),k7_relat_1(sK4,sK5)) != sK5
% 6.60/1.51      | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | v1_funct_1(k7_relat_1(sK4,sK5)) != iProver_top ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_5619,c_2728]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_22,plain,
% 6.60/1.51      ( ~ v1_funct_1(X0)
% 6.60/1.51      | v1_funct_1(k7_relat_1(X0,X1))
% 6.60/1.51      | ~ v1_relat_1(X0) ),
% 6.60/1.51      inference(cnf_transformation,[],[f108]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2792,plain,
% 6.60/1.51      ( v1_funct_1(k7_relat_1(sK4,X0))
% 6.60/1.51      | ~ v1_funct_1(sK4)
% 6.60/1.51      | ~ v1_relat_1(sK4) ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_22]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_4933,plain,
% 6.60/1.51      ( v1_funct_1(k7_relat_1(sK4,sK5))
% 6.60/1.51      | ~ v1_funct_1(sK4)
% 6.60/1.51      | ~ v1_relat_1(sK4) ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_2792]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_4934,plain,
% 6.60/1.51      ( v1_funct_1(k7_relat_1(sK4,sK5)) = iProver_top
% 6.60/1.51      | v1_funct_1(sK4) != iProver_top
% 6.60/1.51      | v1_relat_1(sK4) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_4933]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6128,plain,
% 6.60/1.51      ( m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | k1_relset_1(sK5,u1_struct_0(sK3),k7_relat_1(sK4,sK5)) != sK5 ),
% 6.60/1.51      inference(global_propositional_subsumption,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_5659,c_55,c_57,c_2650,c_4934]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6129,plain,
% 6.60/1.51      ( k1_relset_1(sK5,u1_struct_0(sK3),k7_relat_1(sK4,sK5)) != sK5
% 6.60/1.51      | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top ),
% 6.60/1.51      inference(renaming,[status(thm)],[c_6128]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_8572,plain,
% 6.60/1.51      ( k1_relat_1(k7_relat_1(sK4,sK5)) != sK5
% 6.60/1.51      | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_6674,c_6129]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_12358,plain,
% 6.60/1.51      ( k1_relat_1(k7_relat_1(sK4,sK5)) != sK5 ),
% 6.60/1.51      inference(forward_subsumption_resolution,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_8572,c_6659]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_15320,plain,
% 6.60/1.51      ( sK4 = k1_xboole_0
% 6.60/1.51      | r1_tarski(sK5,k1_relat_1(sK4)) = iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_15269,c_3397]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_16015,plain,
% 6.60/1.51      ( k1_relat_1(k7_relat_1(sK4,sK5)) = sK5
% 6.60/1.51      | sK4 = k1_xboole_0
% 6.60/1.51      | v1_relat_1(sK4) != iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_15320,c_2263]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_16231,plain,
% 6.60/1.51      ( sK4 = k1_xboole_0 ),
% 6.60/1.51      inference(global_propositional_subsumption,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_15723,c_57,c_2650,c_12358,c_16015]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_35,plain,
% 6.60/1.51      ( v1_funct_2(X0,k1_xboole_0,X1)
% 6.60/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 6.60/1.51      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 6.60/1.51      inference(cnf_transformation,[],[f145]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_815,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 6.60/1.51      | ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
% 6.60/1.51      | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 6.60/1.51      | k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != X0
% 6.60/1.51      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(k1_pre_topc(sK2,sK5)) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK3) != X1 ),
% 6.60/1.51      inference(resolution_lifted,[status(thm)],[c_35,c_46]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_816,plain,
% 6.60/1.51      ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
% 6.60/1.51      | ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK3))))
% 6.60/1.51      | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 6.60/1.51      | k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(k1_pre_topc(sK2,sK5)) != k1_xboole_0 ),
% 6.60/1.51      inference(unflattening,[status(thm)],[c_815]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2238,plain,
% 6.60/1.51      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(k1_pre_topc(sK2,sK5)) != k1_xboole_0
% 6.60/1.51      | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_10,plain,
% 6.60/1.51      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 6.60/1.51      inference(cnf_transformation,[],[f141]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2505,plain,
% 6.60/1.51      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(k1_pre_topc(sK2,sK5)) != k1_xboole_0
% 6.60/1.51      | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 6.60/1.51      | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_2238,c_10]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3048,plain,
% 6.60/1.51      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k1_xboole_0
% 6.60/1.51      | sK5 != k1_xboole_0
% 6.60/1.51      | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 6.60/1.51      | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
% 6.60/1.51      inference(light_normalisation,[status(thm)],[c_2505,c_2666]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_5656,plain,
% 6.60/1.51      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k7_relat_1(sK4,sK5)) != k1_xboole_0
% 6.60/1.51      | sK5 != k1_xboole_0
% 6.60/1.51      | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 6.60/1.51      | v1_funct_1(k7_relat_1(sK4,sK5)) != iProver_top ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_5619,c_3048]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_7236,plain,
% 6.60/1.51      ( m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 6.60/1.51      | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | sK5 != k1_xboole_0
% 6.60/1.51      | k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k7_relat_1(sK4,sK5)) != k1_xboole_0 ),
% 6.60/1.51      inference(global_propositional_subsumption,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_5656,c_55,c_57,c_2650,c_4934]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_7237,plain,
% 6.60/1.51      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k7_relat_1(sK4,sK5)) != k1_xboole_0
% 6.60/1.51      | sK5 != k1_xboole_0
% 6.60/1.51      | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.60/1.51      inference(renaming,[status(thm)],[c_7236]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_7244,plain,
% 6.60/1.51      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k7_relat_1(sK4,sK5)) != k1_xboole_0
% 6.60/1.51      | sK5 != k1_xboole_0
% 6.60/1.51      | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.60/1.51      inference(forward_subsumption_resolution,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_7237,c_6659]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_16293,plain,
% 6.60/1.51      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK3),k7_relat_1(k1_xboole_0,sK5)) != k1_xboole_0
% 6.60/1.51      | sK5 != k1_xboole_0
% 6.60/1.51      | m1_subset_1(k7_relat_1(k1_xboole_0,sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_16231,c_7244]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_4056,plain,
% 6.60/1.51      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_2269,c_2257]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_16442,plain,
% 6.60/1.51      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 6.60/1.51      | sK5 != k1_xboole_0
% 6.60/1.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_16293,c_3508,c_4056]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_33,plain,
% 6.60/1.51      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 6.60/1.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 6.60/1.51      | k1_xboole_0 = X0 ),
% 6.60/1.51      inference(cnf_transformation,[],[f143]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_775,plain,
% 6.60/1.51      ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
% 6.60/1.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 6.60/1.51      | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 6.60/1.51      | k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(k1_pre_topc(sK2,sK5)) != X0
% 6.60/1.51      | u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | k1_xboole_0 = X0 ),
% 6.60/1.51      inference(resolution_lifted,[status(thm)],[c_33,c_46]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_776,plain,
% 6.60/1.51      ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
% 6.60/1.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),k1_xboole_0)))
% 6.60/1.51      | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 6.60/1.51      | k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | k1_xboole_0 = u1_struct_0(k1_pre_topc(sK2,sK5)) ),
% 6.60/1.51      inference(unflattening,[status(thm)],[c_775]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_790,plain,
% 6.60/1.51      ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
% 6.60/1.51      | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 6.60/1.51      | k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | k1_xboole_0 = u1_struct_0(k1_pre_topc(sK2,sK5)) ),
% 6.60/1.51      inference(forward_subsumption_resolution,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_776,c_12]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2240,plain,
% 6.60/1.51      ( k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | k1_xboole_0 = u1_struct_0(k1_pre_topc(sK2,sK5))
% 6.60/1.51      | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3039,plain,
% 6.60/1.51      ( k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(k1_pre_topc(sK2,sK5)) = k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
% 6.60/1.51      inference(light_normalisation,[status(thm)],[c_2240,c_2666]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_3040,plain,
% 6.60/1.51      ( k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | sK5 = k1_xboole_0
% 6.60/1.51      | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_3039,c_2666]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_5657,plain,
% 6.60/1.51      ( k7_relat_1(sK4,sK5) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | sK5 = k1_xboole_0
% 6.60/1.51      | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | v1_funct_1(k7_relat_1(sK4,sK5)) != iProver_top ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_5619,c_3040]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6833,plain,
% 6.60/1.51      ( m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | sK5 = k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | k7_relat_1(sK4,sK5) != k1_xboole_0 ),
% 6.60/1.51      inference(global_propositional_subsumption,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_5657,c_55,c_57,c_2650,c_4934]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6834,plain,
% 6.60/1.51      ( k7_relat_1(sK4,sK5) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | sK5 = k1_xboole_0
% 6.60/1.51      | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top ),
% 6.60/1.51      inference(renaming,[status(thm)],[c_6833]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6841,plain,
% 6.60/1.51      ( k7_relat_1(sK4,sK5) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | sK5 = k1_xboole_0 ),
% 6.60/1.51      inference(forward_subsumption_resolution,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_6834,c_6659]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_16295,plain,
% 6.60/1.51      ( k7_relat_1(k1_xboole_0,sK5) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | sK5 = k1_xboole_0 ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_16231,c_6841]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_16428,plain,
% 6.60/1.51      ( u1_struct_0(sK3) != k1_xboole_0
% 6.60/1.51      | sK5 = k1_xboole_0
% 6.60/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_16295,c_3508]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_16429,plain,
% 6.60/1.51      ( u1_struct_0(sK3) != k1_xboole_0 | sK5 = k1_xboole_0 ),
% 6.60/1.51      inference(equality_resolution_simp,[status(thm)],[c_16428]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_847,plain,
% 6.60/1.51      ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
% 6.60/1.51      | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 6.60/1.51      | k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != sK4
% 6.60/1.51      | u1_struct_0(k1_pre_topc(sK2,sK5)) != u1_struct_0(sK2)
% 6.60/1.51      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 6.60/1.51      inference(resolution_lifted,[status(thm)],[c_46,c_49]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_956,plain,
% 6.60/1.51      ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3))))
% 6.60/1.51      | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 6.60/1.51      | k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != sK4
% 6.60/1.51      | u1_struct_0(k1_pre_topc(sK2,sK5)) != u1_struct_0(sK2) ),
% 6.60/1.51      inference(equality_resolution_simp,[status(thm)],[c_847]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2236,plain,
% 6.60/1.51      ( k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != sK4
% 6.60/1.51      | u1_struct_0(k1_pre_topc(sK2,sK5)) != u1_struct_0(sK2)
% 6.60/1.51      | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK5)),u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_956]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2991,plain,
% 6.60/1.51      ( k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != sK4
% 6.60/1.51      | u1_struct_0(sK2) != sK5
% 6.60/1.51      | m1_subset_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | v1_funct_1(k5_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != iProver_top ),
% 6.60/1.51      inference(light_normalisation,[status(thm)],[c_2236,c_2666]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_5658,plain,
% 6.60/1.51      ( k7_relat_1(sK4,sK5) != sK4
% 6.60/1.51      | u1_struct_0(sK2) != sK5
% 6.60/1.51      | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | v1_funct_1(k7_relat_1(sK4,sK5)) != iProver_top ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_5619,c_2991]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6711,plain,
% 6.60/1.51      ( m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top
% 6.60/1.51      | u1_struct_0(sK2) != sK5
% 6.60/1.51      | k7_relat_1(sK4,sK5) != sK4 ),
% 6.60/1.51      inference(global_propositional_subsumption,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_5658,c_55,c_57,c_2650,c_4934]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6712,plain,
% 6.60/1.51      ( k7_relat_1(sK4,sK5) != sK4
% 6.60/1.51      | u1_struct_0(sK2) != sK5
% 6.60/1.51      | m1_subset_1(k7_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,u1_struct_0(sK3)))) != iProver_top ),
% 6.60/1.51      inference(renaming,[status(thm)],[c_6711]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_6718,plain,
% 6.60/1.51      ( k7_relat_1(sK4,sK5) != sK4 | u1_struct_0(sK2) != sK5 ),
% 6.60/1.51      inference(forward_subsumption_resolution,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_6712,c_6659]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_16296,plain,
% 6.60/1.51      ( k7_relat_1(k1_xboole_0,sK5) != k1_xboole_0
% 6.60/1.51      | u1_struct_0(sK2) != sK5 ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_16231,c_6718]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_16422,plain,
% 6.60/1.51      ( u1_struct_0(sK2) != sK5 | k1_xboole_0 != k1_xboole_0 ),
% 6.60/1.51      inference(demodulation,[status(thm)],[c_16296,c_3508]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_16423,plain,
% 6.60/1.51      ( u1_struct_0(sK2) != sK5 ),
% 6.60/1.51      inference(equality_resolution_simp,[status(thm)],[c_16422]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_31,plain,
% 6.60/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 6.60/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | ~ v1_funct_1(X0)
% 6.60/1.51      | ~ v1_xboole_0(X0)
% 6.60/1.51      | v1_xboole_0(X1)
% 6.60/1.51      | v1_xboole_0(X2) ),
% 6.60/1.51      inference(cnf_transformation,[],[f116]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_21,plain,
% 6.60/1.51      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 6.60/1.51      inference(cnf_transformation,[],[f106]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_290,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | ~ v1_funct_2(X0,X1,X2)
% 6.60/1.51      | ~ v1_xboole_0(X0)
% 6.60/1.51      | v1_xboole_0(X1)
% 6.60/1.51      | v1_xboole_0(X2) ),
% 6.60/1.51      inference(global_propositional_subsumption,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_31,c_21]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_291,plain,
% 6.60/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 6.60/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | ~ v1_xboole_0(X0)
% 6.60/1.51      | v1_xboole_0(X1)
% 6.60/1.51      | v1_xboole_0(X2) ),
% 6.60/1.51      inference(renaming,[status(thm)],[c_290]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_743,plain,
% 6.60/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.60/1.51      | ~ v1_xboole_0(X0)
% 6.60/1.51      | v1_xboole_0(X1)
% 6.60/1.51      | v1_xboole_0(X2)
% 6.60/1.51      | u1_struct_0(sK3) != X2
% 6.60/1.51      | u1_struct_0(sK2) != X1
% 6.60/1.51      | sK4 != X0 ),
% 6.60/1.51      inference(resolution_lifted,[status(thm)],[c_291,c_49]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_744,plain,
% 6.60/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 6.60/1.51      | v1_xboole_0(u1_struct_0(sK3))
% 6.60/1.51      | v1_xboole_0(u1_struct_0(sK2))
% 6.60/1.51      | ~ v1_xboole_0(sK4) ),
% 6.60/1.51      inference(unflattening,[status(thm)],[c_743]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_746,plain,
% 6.60/1.51      ( v1_xboole_0(u1_struct_0(sK3))
% 6.60/1.51      | v1_xboole_0(u1_struct_0(sK2))
% 6.60/1.51      | ~ v1_xboole_0(sK4) ),
% 6.60/1.51      inference(global_propositional_subsumption,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_744,c_48]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2241,plain,
% 6.60/1.51      ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 6.60/1.51      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 6.60/1.51      | v1_xboole_0(sK4) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2270,plain,
% 6.60/1.51      ( X0 = X1
% 6.60/1.51      | v1_xboole_0(X0) != iProver_top
% 6.60/1.51      | v1_xboole_0(X1) != iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_4049,plain,
% 6.60/1.51      ( u1_struct_0(sK3) = X0
% 6.60/1.51      | v1_xboole_0(X0) != iProver_top
% 6.60/1.51      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 6.60/1.51      | v1_xboole_0(sK4) != iProver_top ),
% 6.60/1.51      inference(superposition,[status(thm)],[c_2241,c_2270]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_4051,plain,
% 6.60/1.51      ( u1_struct_0(sK3) = k1_xboole_0
% 6.60/1.51      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 6.60/1.51      | v1_xboole_0(sK4) != iProver_top
% 6.60/1.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_4049]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_1289,plain,
% 6.60/1.51      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 6.60/1.51      theory(equality) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2753,plain,
% 6.60/1.51      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_1289]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2754,plain,
% 6.60/1.51      ( sK4 != X0
% 6.60/1.51      | v1_xboole_0(X0) != iProver_top
% 6.60/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_2753]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_2756,plain,
% 6.60/1.51      ( sK4 != k1_xboole_0
% 6.60/1.51      | v1_xboole_0(sK4) = iProver_top
% 6.60/1.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_2754]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_147,plain,
% 6.60/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 6.60/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(c_149,plain,
% 6.60/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 6.60/1.51      inference(instantiation,[status(thm)],[c_147]) ).
% 6.60/1.51  
% 6.60/1.51  cnf(contradiction,plain,
% 6.60/1.51      ( $false ),
% 6.60/1.51      inference(minisat,
% 6.60/1.51                [status(thm)],
% 6.60/1.51                [c_19727,c_18274,c_16442,c_16429,c_16423,c_16015,c_12358,
% 6.60/1.51                 c_7415,c_4051,c_3331,c_2910,c_2756,c_2650,c_170,c_149,
% 6.60/1.51                 c_57]) ).
% 6.60/1.51  
% 6.60/1.51  
% 6.60/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 6.60/1.51  
% 6.60/1.51  ------                               Statistics
% 6.60/1.51  
% 6.60/1.51  ------ General
% 6.60/1.51  
% 6.60/1.51  abstr_ref_over_cycles:                  0
% 6.60/1.51  abstr_ref_under_cycles:                 0
% 6.60/1.51  gc_basic_clause_elim:                   0
% 6.60/1.51  forced_gc_time:                         0
% 6.60/1.51  parsing_time:                           0.015
% 6.60/1.51  unif_index_cands_time:                  0.
% 6.60/1.51  unif_index_add_time:                    0.
% 6.60/1.51  orderings_time:                         0.
% 6.60/1.51  out_proof_time:                         0.017
% 6.60/1.51  total_time:                             0.598
% 6.60/1.51  num_of_symbols:                         56
% 6.60/1.51  num_of_terms:                           17101
% 6.60/1.51  
% 6.60/1.51  ------ Preprocessing
% 6.60/1.51  
% 6.60/1.51  num_of_splits:                          0
% 6.60/1.51  num_of_split_atoms:                     0
% 6.60/1.51  num_of_reused_defs:                     0
% 6.60/1.51  num_eq_ax_congr_red:                    32
% 6.60/1.51  num_of_sem_filtered_clauses:            1
% 6.60/1.51  num_of_subtypes:                        0
% 6.60/1.51  monotx_restored_types:                  0
% 6.60/1.51  sat_num_of_epr_types:                   0
% 6.60/1.51  sat_num_of_non_cyclic_types:            0
% 6.60/1.51  sat_guarded_non_collapsed_types:        0
% 6.60/1.51  num_pure_diseq_elim:                    0
% 6.60/1.51  simp_replaced_by:                       0
% 6.60/1.51  res_preprocessed:                       219
% 6.60/1.51  prep_upred:                             0
% 6.60/1.51  prep_unflattend:                        53
% 6.60/1.51  smt_new_axioms:                         0
% 6.60/1.51  pred_elim_cands:                        6
% 6.60/1.51  pred_elim:                              3
% 6.60/1.51  pred_elim_cl:                           2
% 6.60/1.51  pred_elim_cycles:                       5
% 6.60/1.51  merged_defs:                            8
% 6.60/1.51  merged_defs_ncl:                        0
% 6.60/1.51  bin_hyper_res:                          9
% 6.60/1.51  prep_cycles:                            4
% 6.60/1.51  pred_elim_time:                         0.014
% 6.60/1.51  splitting_time:                         0.
% 6.60/1.51  sem_filter_time:                        0.
% 6.60/1.51  monotx_time:                            0.001
% 6.60/1.51  subtype_inf_time:                       0.
% 6.60/1.51  
% 6.60/1.51  ------ Problem properties
% 6.60/1.51  
% 6.60/1.51  clauses:                                46
% 6.60/1.51  conjectures:                            3
% 6.60/1.51  epr:                                    9
% 6.60/1.51  horn:                                   38
% 6.60/1.51  ground:                                 11
% 6.60/1.51  unary:                                  7
% 6.60/1.51  binary:                                 17
% 6.60/1.51  lits:                                   117
% 6.60/1.51  lits_eq:                                34
% 6.60/1.51  fd_pure:                                0
% 6.60/1.51  fd_pseudo:                              0
% 6.60/1.51  fd_cond:                                2
% 6.60/1.51  fd_pseudo_cond:                         2
% 6.60/1.51  ac_symbols:                             0
% 6.60/1.51  
% 6.60/1.51  ------ Propositional Solver
% 6.60/1.51  
% 6.60/1.51  prop_solver_calls:                      29
% 6.60/1.51  prop_fast_solver_calls:                 1915
% 6.60/1.51  smt_solver_calls:                       0
% 6.60/1.51  smt_fast_solver_calls:                  0
% 6.60/1.51  prop_num_of_clauses:                    7617
% 6.60/1.51  prop_preprocess_simplified:             15690
% 6.60/1.51  prop_fo_subsumed:                       85
% 6.60/1.51  prop_solver_time:                       0.
% 6.60/1.51  smt_solver_time:                        0.
% 6.60/1.51  smt_fast_solver_time:                   0.
% 6.60/1.51  prop_fast_solver_time:                  0.
% 6.60/1.51  prop_unsat_core_time:                   0.
% 6.60/1.51  
% 6.60/1.51  ------ QBF
% 6.60/1.51  
% 6.60/1.51  qbf_q_res:                              0
% 6.60/1.51  qbf_num_tautologies:                    0
% 6.60/1.51  qbf_prep_cycles:                        0
% 6.60/1.51  
% 6.60/1.51  ------ BMC1
% 6.60/1.51  
% 6.60/1.51  bmc1_current_bound:                     -1
% 6.60/1.51  bmc1_last_solved_bound:                 -1
% 6.60/1.51  bmc1_unsat_core_size:                   -1
% 6.60/1.51  bmc1_unsat_core_parents_size:           -1
% 6.60/1.51  bmc1_merge_next_fun:                    0
% 6.60/1.51  bmc1_unsat_core_clauses_time:           0.
% 6.60/1.51  
% 6.60/1.51  ------ Instantiation
% 6.60/1.51  
% 6.60/1.51  inst_num_of_clauses:                    2002
% 6.60/1.51  inst_num_in_passive:                    239
% 6.60/1.51  inst_num_in_active:                     785
% 6.60/1.51  inst_num_in_unprocessed:                979
% 6.60/1.51  inst_num_of_loops:                      1140
% 6.60/1.51  inst_num_of_learning_restarts:          0
% 6.60/1.51  inst_num_moves_active_passive:          352
% 6.60/1.51  inst_lit_activity:                      0
% 6.60/1.51  inst_lit_activity_moves:                0
% 6.60/1.51  inst_num_tautologies:                   0
% 6.60/1.51  inst_num_prop_implied:                  0
% 6.60/1.51  inst_num_existing_simplified:           0
% 6.60/1.51  inst_num_eq_res_simplified:             0
% 6.60/1.51  inst_num_child_elim:                    0
% 6.60/1.51  inst_num_of_dismatching_blockings:      610
% 6.60/1.51  inst_num_of_non_proper_insts:           1777
% 6.60/1.51  inst_num_of_duplicates:                 0
% 6.60/1.51  inst_inst_num_from_inst_to_res:         0
% 6.60/1.51  inst_dismatching_checking_time:         0.
% 6.60/1.51  
% 6.60/1.51  ------ Resolution
% 6.60/1.51  
% 6.60/1.51  res_num_of_clauses:                     0
% 6.60/1.51  res_num_in_passive:                     0
% 6.60/1.51  res_num_in_active:                      0
% 6.60/1.51  res_num_of_loops:                       223
% 6.60/1.51  res_forward_subset_subsumed:            44
% 6.60/1.51  res_backward_subset_subsumed:           2
% 6.60/1.51  res_forward_subsumed:                   1
% 6.60/1.51  res_backward_subsumed:                  0
% 6.60/1.51  res_forward_subsumption_resolution:     1
% 6.60/1.51  res_backward_subsumption_resolution:    0
% 6.60/1.51  res_clause_to_clause_subsumption:       1611
% 6.60/1.51  res_orphan_elimination:                 0
% 6.60/1.51  res_tautology_del:                      110
% 6.60/1.51  res_num_eq_res_simplified:              1
% 6.60/1.51  res_num_sel_changes:                    0
% 6.60/1.51  res_moves_from_active_to_pass:          0
% 6.60/1.51  
% 6.60/1.51  ------ Superposition
% 6.60/1.51  
% 6.60/1.51  sup_time_total:                         0.
% 6.60/1.51  sup_time_generating:                    0.
% 6.60/1.51  sup_time_sim_full:                      0.
% 6.60/1.51  sup_time_sim_immed:                     0.
% 6.60/1.51  
% 6.60/1.51  sup_num_of_clauses:                     414
% 6.60/1.51  sup_num_in_active:                      98
% 6.60/1.51  sup_num_in_passive:                     316
% 6.60/1.51  sup_num_of_loops:                       227
% 6.60/1.51  sup_fw_superposition:                   337
% 6.60/1.51  sup_bw_superposition:                   484
% 6.60/1.51  sup_immediate_simplified:               294
% 6.60/1.51  sup_given_eliminated:                   0
% 6.60/1.51  comparisons_done:                       0
% 6.60/1.51  comparisons_avoided:                    81
% 6.60/1.51  
% 6.60/1.51  ------ Simplifications
% 6.60/1.51  
% 6.60/1.51  
% 6.60/1.51  sim_fw_subset_subsumed:                 84
% 6.60/1.51  sim_bw_subset_subsumed:                 34
% 6.60/1.51  sim_fw_subsumed:                        66
% 6.60/1.51  sim_bw_subsumed:                        7
% 6.60/1.51  sim_fw_subsumption_res:                 9
% 6.60/1.51  sim_bw_subsumption_res:                 2
% 6.60/1.51  sim_tautology_del:                      19
% 6.60/1.51  sim_eq_tautology_del:                   65
% 6.60/1.51  sim_eq_res_simp:                        4
% 6.60/1.51  sim_fw_demodulated:                     101
% 6.60/1.51  sim_bw_demodulated:                     122
% 6.60/1.51  sim_light_normalised:                   123
% 6.60/1.51  sim_joinable_taut:                      0
% 6.60/1.51  sim_joinable_simp:                      0
% 6.60/1.51  sim_ac_normalised:                      0
% 6.60/1.51  sim_smt_subsumption:                    0
% 6.60/1.51  
%------------------------------------------------------------------------------
