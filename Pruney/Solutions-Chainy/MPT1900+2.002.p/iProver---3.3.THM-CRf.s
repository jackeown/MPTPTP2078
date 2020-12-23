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
% DateTime   : Thu Dec  3 12:27:51 EST 2020

% Result     : Theorem 15.38s
% Output     : CNFRefutation 15.38s
% Verified   : 
% Statistics : Number of formulae       :  251 (2901 expanded)
%              Number of clauses        :  157 ( 797 expanded)
%              Number of leaves         :   27 ( 878 expanded)
%              Depth                    :   28
%              Number of atoms          : 1088 (20977 expanded)
%              Number of equality atoms :  384 (1719 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f69])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f155,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f104])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f106,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f105,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f107,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f61])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v5_pre_topc(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ v5_pre_topc(sK7,X0,X1)
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ~ v5_pre_topc(X2,X0,sK6)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK6))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK6)
        & v2_pre_topc(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v5_pre_topc(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,sK5,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK5)
      & v1_tdlat_3(sK5)
      & v2_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    & v1_funct_1(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & l1_pre_topc(sK5)
    & v1_tdlat_3(sK5)
    & v2_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f62,f91,f90,f89])).

fof(f146,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f92])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f121,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f120,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f151,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f92])).

fof(f148,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f92])).

fof(f23,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f73,plain,(
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
    inference(nnf_transformation,[],[f52])).

fof(f74,plain,(
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
    inference(rectify,[],[f73])).

fof(f75,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0)
        & v3_pre_topc(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0)
                    & v3_pre_topc(sK1(X0,X1,X2),X1)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f74,f75])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f150,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f92])).

fof(f149,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f92])).

fof(f152,plain,(
    ~ v5_pre_topc(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f92])).

fof(f144,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f92])).

fof(f145,plain,(
    v1_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f92])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f81,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f82,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f81])).

fof(f83,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f82,f83])).

fof(f138,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f67])).

fof(f99,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f24,axiom,(
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
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f77])).

fof(f79,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2))))
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2))))
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f78,f79])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f147,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f92])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f85,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f86,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f85])).

fof(f87,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK4(X0),X0)
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f86,f87])).

fof(f141,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f137,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f155])).

cnf(c_13,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_5237,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_5270,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5237,c_12])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_5231,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_11456,plain,
    ( k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1) = k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5270,c_5231])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_5232,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_10015,plain,
    ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5270,c_5232])).

cnf(c_46889,plain,
    ( k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_11456,c_10015])).

cnf(c_46892,plain,
    ( k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_9,c_46889])).

cnf(c_46920,plain,
    ( k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_46892,c_9])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_5233,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_5234,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12800,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5233,c_5234])).

cnf(c_59528,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_46920,c_12800])).

cnf(c_59668,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_59528,c_9])).

cnf(c_14,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_177,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_179,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_59725,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_59668,c_179])).

cnf(c_57,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_5219,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_28,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_27,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_723,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_28,c_27])).

cnf(c_5216,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_10857,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
    inference(superposition,[status(thm)],[c_5219,c_5216])).

cnf(c_52,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_5222,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_8511,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5222,c_5234])).

cnf(c_11496,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK6))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10857,c_8511])).

cnf(c_55,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_5221,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_10856,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_5221,c_5216])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_53,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_1389,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | k2_struct_0(X2) = k1_xboole_0
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_53])).

cnf(c_1390,plain,
    ( v5_pre_topc(sK7,X0,X1)
    | m1_subset_1(sK1(X0,X1,sK7),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK7)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | k2_struct_0(X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1389])).

cnf(c_54,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_1394,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | m1_subset_1(sK1(X0,X1,sK7),k1_zfmisc_1(u1_struct_0(X1)))
    | v5_pre_topc(sK7,X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | k2_struct_0(X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1390,c_54])).

cnf(c_1395,plain,
    ( v5_pre_topc(sK7,X0,X1)
    | m1_subset_1(sK1(X0,X1,sK7),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | k2_struct_0(X1) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1394])).

cnf(c_5206,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | k2_struct_0(X0) = k1_xboole_0
    | v5_pre_topc(sK7,X1,X0) = iProver_top
    | m1_subset_1(sK1(X1,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1395])).

cnf(c_6679,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | k2_struct_0(X0) = k1_xboole_0
    | v5_pre_topc(sK7,sK5,X0) = iProver_top
    | m1_subset_1(sK1(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5206])).

cnf(c_62,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_4159,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6041,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_4159])).

cnf(c_6046,plain,
    ( v5_pre_topc(sK7,sK5,X0)
    | m1_subset_1(sK1(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | k2_struct_0(X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1395])).

cnf(c_6047,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | k2_struct_0(X0) = k1_xboole_0
    | v5_pre_topc(sK7,sK5,X0) = iProver_top
    | m1_subset_1(sK1(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6046])).

cnf(c_8047,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(sK1(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v5_pre_topc(sK7,sK5,X0) = iProver_top
    | k2_struct_0(X0) = k1_xboole_0
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6679,c_62,c_6041,c_6047])).

cnf(c_8048,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | k2_struct_0(X0) = k1_xboole_0
    | v5_pre_topc(sK7,sK5,X0) = iProver_top
    | m1_subset_1(sK1(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8047])).

cnf(c_8059,plain,
    ( k2_struct_0(sK6) = k1_xboole_0
    | v5_pre_topc(sK7,sK5,sK6) = iProver_top
    | m1_subset_1(sK1(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_8048])).

cnf(c_64,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_67,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_51,negated_conjecture,
    ( ~ v5_pre_topc(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_68,plain,
    ( v5_pre_topc(sK7,sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_8956,plain,
    ( k2_struct_0(sK6) = k1_xboole_0
    | m1_subset_1(sK1(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8059,c_64,c_67,c_68])).

cnf(c_8962,plain,
    ( k2_struct_0(sK6) = k1_xboole_0
    | r1_tarski(sK1(sK5,sK6,sK7),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8956,c_5234])).

cnf(c_59,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_58,negated_conjecture,
    ( v1_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1533,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | k2_struct_0(X2) = k1_xboole_0
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_53])).

cnf(c_1534,plain,
    ( v5_pre_topc(sK7,X0,X1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK1(X0,X1,sK7)),X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK7)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | k2_struct_0(X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1533])).

cnf(c_1538,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK1(X0,X1,sK7)),X0)
    | v5_pre_topc(sK7,X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | k2_struct_0(X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1534,c_54])).

cnf(c_1539,plain,
    ( v5_pre_topc(sK7,X0,X1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK1(X0,X1,sK7)),X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | k2_struct_0(X1) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1538])).

cnf(c_2410,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK1(X0,X1,sK7)),X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | k2_struct_0(X1) = k1_xboole_0
    | sK6 != X1
    | sK5 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_51,c_1539])).

cnf(c_2411,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | k2_struct_0(sK6) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_2410])).

cnf(c_2413,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | k2_struct_0(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2411,c_57,c_55,c_52])).

cnf(c_7391,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4159])).

cnf(c_47,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_5965,plain,
    ( v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v1_tdlat_3(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_6417,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK5),X0,X1,X2),sK5)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK5),X0,X1,X2),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v1_tdlat_3(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_5965])).

cnf(c_6974,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,X0),sK5)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v1_tdlat_3(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_6417])).

cnf(c_7751,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v1_tdlat_3(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_6974])).

cnf(c_5981,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_9922,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(instantiation,[status(thm)],[c_5981])).

cnf(c_10518,plain,
    ( k2_struct_0(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8962,c_59,c_58,c_57,c_52,c_2413,c_6041,c_7391,c_7751,c_9922])).

cnf(c_10861,plain,
    ( u1_struct_0(sK6) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10856,c_10518])).

cnf(c_12283,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(k2_struct_0(sK5),k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11496,c_10861])).

cnf(c_12284,plain,
    ( r1_tarski(sK7,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12283,c_9])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_5241,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_12287,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_12284,c_5241])).

cnf(c_12288,plain,
    ( ~ r1_tarski(k1_xboole_0,sK7)
    | sK7 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12287])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_22610,plain,
    ( r1_tarski(k1_xboole_0,sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_49597,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12287,c_12288,c_22610])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1227,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_53])).

cnf(c_1228,plain,
    ( v5_pre_topc(sK7,X0,X1)
    | m1_subset_1(sK2(X0,X1,sK7),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK7)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1227])).

cnf(c_1232,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | m1_subset_1(sK2(X0,X1,sK7),k1_zfmisc_1(u1_struct_0(X1)))
    | v5_pre_topc(sK7,X0,X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1228,c_54])).

cnf(c_1233,plain,
    ( v5_pre_topc(sK7,X0,X1)
    | m1_subset_1(sK2(X0,X1,sK7),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5) ),
    inference(renaming,[status(thm)],[c_1232])).

cnf(c_5210,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | v5_pre_topc(sK7,X1,X0) = iProver_top
    | m1_subset_1(sK2(X1,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(c_7270,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | v5_pre_topc(sK7,sK5,X0) = iProver_top
    | m1_subset_1(sK2(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5210])).

cnf(c_60,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_6044,plain,
    ( v5_pre_topc(sK7,sK5,X0)
    | m1_subset_1(sK2(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1233])).

cnf(c_6055,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | v5_pre_topc(sK7,sK5,X0) = iProver_top
    | m1_subset_1(sK2(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6044])).

cnf(c_8141,plain,
    ( l1_pre_topc(X0) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | v5_pre_topc(sK7,sK5,X0) = iProver_top
    | m1_subset_1(sK2(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7270,c_60,c_62,c_6041,c_6055])).

cnf(c_8142,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | v5_pre_topc(sK7,sK5,X0) = iProver_top
    | m1_subset_1(sK2(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8141])).

cnf(c_8153,plain,
    ( v5_pre_topc(sK7,sK5,sK6) = iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_8142])).

cnf(c_56,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_63,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_2527,plain,
    ( m1_subset_1(sK2(X0,X1,sK7),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | sK6 != X1
    | sK5 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_51,c_1233])).

cnf(c_2528,plain,
    ( m1_subset_1(sK2(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_2527])).

cnf(c_2529,plain,
    ( u1_struct_0(sK6) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | m1_subset_1(sK2(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2528])).

cnf(c_9287,plain,
    ( m1_subset_1(sK2(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8153,c_60,c_62,c_63,c_64,c_67,c_2529,c_6041,c_7391])).

cnf(c_9292,plain,
    ( r1_tarski(sK2(sK5,sK6,sK7),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9287,c_5234])).

cnf(c_10276,plain,
    ( sK2(sK5,sK6,sK7) = u1_struct_0(sK6)
    | r1_tarski(u1_struct_0(sK6),sK2(sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9292,c_5241])).

cnf(c_12131,plain,
    ( sK2(sK5,sK6,sK7) = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK2(sK5,sK6,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10861,c_10276])).

cnf(c_5239,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_20361,plain,
    ( sK2(sK5,sK6,sK7) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12131,c_5239])).

cnf(c_39,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK2(X1,X2,X0))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_1266,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK2(X1,X2,X0))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_53])).

cnf(c_1267,plain,
    ( v5_pre_topc(sK7,X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK2(X0,X1,sK7))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,k2_pre_topc(X1,sK2(X0,X1,sK7))))
    | ~ v1_funct_1(sK7)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1266])).

cnf(c_1271,plain,
    ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK2(X0,X1,sK7))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,k2_pre_topc(X1,sK2(X0,X1,sK7))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v5_pre_topc(sK7,X0,X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1267,c_54])).

cnf(c_1272,plain,
    ( v5_pre_topc(sK7,X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK2(X0,X1,sK7))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,k2_pre_topc(X1,sK2(X0,X1,sK7))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5) ),
    inference(renaming,[status(thm)],[c_1271])).

cnf(c_5209,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | v5_pre_topc(sK7,X1,X0) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK7,sK2(X1,X0,sK7))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK7,k2_pre_topc(X0,sK2(X1,X0,sK7)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1272])).

cnf(c_6320,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | v5_pre_topc(sK7,sK5,X0) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,sK2(sK5,X0,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,k2_pre_topc(X0,sK2(sK5,X0,sK7)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5209])).

cnf(c_6042,plain,
    ( v5_pre_topc(sK7,sK5,X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,sK2(sK5,X0,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,k2_pre_topc(X0,sK2(sK5,X0,sK7))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1272])).

cnf(c_6063,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | v5_pre_topc(sK7,sK5,X0) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,sK2(sK5,X0,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,k2_pre_topc(X0,sK2(sK5,X0,sK7)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6042])).

cnf(c_7538,plain,
    ( l1_pre_topc(X0) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | v5_pre_topc(sK7,sK5,X0) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,sK2(sK5,X0,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,k2_pre_topc(X0,sK2(sK5,X0,sK7)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6320,c_60,c_62,c_6041,c_6063])).

cnf(c_7539,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | v5_pre_topc(sK7,sK5,X0) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,sK2(sK5,X0,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,k2_pre_topc(X0,sK2(sK5,X0,sK7)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7538])).

cnf(c_7550,plain,
    ( v5_pre_topc(sK7,sK5,sK6) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK2(sK5,sK6,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,k2_pre_topc(sK6,sK2(sK5,sK6,sK7)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_7539])).

cnf(c_2510,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK2(X0,X1,sK7))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,k2_pre_topc(X1,sK2(X0,X1,sK7))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | sK6 != X1
    | sK5 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_51,c_1272])).

cnf(c_2511,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK2(sK5,sK6,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,k2_pre_topc(sK6,sK2(sK5,sK6,sK7))))
    | ~ v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_2510])).

cnf(c_2512,plain,
    ( u1_struct_0(sK6) != u1_struct_0(sK6)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK2(sK5,sK6,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,k2_pre_topc(sK6,sK2(sK5,sK6,sK7)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2511])).

cnf(c_8403,plain,
    ( r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK2(sK5,sK6,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,k2_pre_topc(sK6,sK2(sK5,sK6,sK7)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7550,c_60,c_62,c_63,c_64,c_67,c_2512,c_6041,c_7391])).

cnf(c_11497,plain,
    ( r1_tarski(k2_pre_topc(sK5,k8_relset_1(k2_struct_0(sK5),u1_struct_0(sK6),sK7,sK2(sK5,sK6,sK7))),k8_relset_1(k2_struct_0(sK5),u1_struct_0(sK6),sK7,k2_pre_topc(sK6,sK2(sK5,sK6,sK7)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10857,c_8403])).

cnf(c_13247,plain,
    ( r1_tarski(k2_pre_topc(sK5,k8_relset_1(k2_struct_0(sK5),k1_xboole_0,sK7,sK2(sK5,sK6,sK7))),k8_relset_1(k2_struct_0(sK5),k1_xboole_0,sK7,k2_pre_topc(sK6,sK2(sK5,sK6,sK7)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11497,c_10861])).

cnf(c_20364,plain,
    ( r1_tarski(k2_pre_topc(sK5,k8_relset_1(k2_struct_0(sK5),k1_xboole_0,sK7,k1_xboole_0)),k8_relset_1(k2_struct_0(sK5),k1_xboole_0,sK7,k2_pre_topc(sK6,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20361,c_13247])).

cnf(c_11454,plain,
    ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,u1_struct_0(sK6)) = k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7) ),
    inference(superposition,[status(thm)],[c_5222,c_5231])).

cnf(c_10013,plain,
    ( k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_5222,c_5232])).

cnf(c_11476,plain,
    ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,u1_struct_0(sK6)) = k1_relat_1(sK7) ),
    inference(light_normalisation,[status(thm)],[c_11454,c_10013])).

cnf(c_12463,plain,
    ( k8_relset_1(k2_struct_0(sK5),k1_xboole_0,sK7,k1_xboole_0) = k1_relat_1(sK7) ),
    inference(light_normalisation,[status(thm)],[c_11476,c_10857,c_10861])).

cnf(c_12799,plain,
    ( m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12463,c_5233])).

cnf(c_12867,plain,
    ( m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12799,c_9])).

cnf(c_11521,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10857,c_5222])).

cnf(c_12130,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10861,c_11521])).

cnf(c_12148,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12130,c_9])).

cnf(c_13757,plain,
    ( m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12867,c_12148])).

cnf(c_50,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_30,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_872,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(resolution,[status(thm)],[c_50,c_30])).

cnf(c_44,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_886,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_872,c_44])).

cnf(c_5213,plain,
    ( k2_pre_topc(X0,X1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_886])).

cnf(c_11943,plain,
    ( k2_pre_topc(sK5,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK5))) != iProver_top
    | v1_tdlat_3(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_10857,c_5213])).

cnf(c_61,plain,
    ( v1_tdlat_3(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_13210,plain,
    ( k2_pre_topc(sK5,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11943,c_61,c_62])).

cnf(c_13763,plain,
    ( k2_pre_topc(sK5,k1_relat_1(sK7)) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_13757,c_13210])).

cnf(c_20371,plain,
    ( r1_tarski(k1_relat_1(sK7),k8_relset_1(k2_struct_0(sK5),k1_xboole_0,sK7,k2_pre_topc(sK6,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20364,c_12463,c_13763])).

cnf(c_49688,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK5),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK6,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_49597,c_20371])).

cnf(c_59756,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_59725,c_49688])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.38/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.38/2.49  
% 15.38/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.38/2.49  
% 15.38/2.49  ------  iProver source info
% 15.38/2.49  
% 15.38/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.38/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.38/2.49  git: non_committed_changes: false
% 15.38/2.49  git: last_make_outside_of_git: false
% 15.38/2.49  
% 15.38/2.49  ------ 
% 15.38/2.49  ------ Parsing...
% 15.38/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.38/2.49  
% 15.38/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 15.38/2.49  
% 15.38/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.38/2.49  
% 15.38/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.38/2.49  ------ Proving...
% 15.38/2.49  ------ Problem Properties 
% 15.38/2.49  
% 15.38/2.49  
% 15.38/2.49  clauses                                 48
% 15.38/2.49  conjectures                             7
% 15.38/2.49  EPR                                     14
% 15.38/2.49  Horn                                    37
% 15.38/2.49  unary                                   16
% 15.38/2.49  binary                                  9
% 15.38/2.49  lits                                    173
% 15.38/2.49  lits eq                                 46
% 15.38/2.49  fd_pure                                 0
% 15.38/2.49  fd_pseudo                               0
% 15.38/2.49  fd_cond                                 2
% 15.38/2.49  fd_pseudo_cond                          2
% 15.38/2.49  AC symbols                              0
% 15.38/2.49  
% 15.38/2.49  ------ Input Options Time Limit: Unbounded
% 15.38/2.49  
% 15.38/2.49  
% 15.38/2.49  ------ 
% 15.38/2.49  Current options:
% 15.38/2.49  ------ 
% 15.38/2.49  
% 15.38/2.49  
% 15.38/2.49  
% 15.38/2.49  
% 15.38/2.49  ------ Proving...
% 15.38/2.49  
% 15.38/2.49  
% 15.38/2.49  % SZS status Theorem for theBenchmark.p
% 15.38/2.49  
% 15.38/2.49   Resolution empty clause
% 15.38/2.49  
% 15.38/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.38/2.49  
% 15.38/2.49  fof(f7,axiom,(
% 15.38/2.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f69,plain,(
% 15.38/2.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.38/2.49    inference(nnf_transformation,[],[f7])).
% 15.38/2.49  
% 15.38/2.49  fof(f70,plain,(
% 15.38/2.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.38/2.49    inference(flattening,[],[f69])).
% 15.38/2.49  
% 15.38/2.49  fof(f104,plain,(
% 15.38/2.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 15.38/2.49    inference(cnf_transformation,[],[f70])).
% 15.38/2.49  
% 15.38/2.49  fof(f155,plain,(
% 15.38/2.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 15.38/2.49    inference(equality_resolution,[],[f104])).
% 15.38/2.49  
% 15.38/2.49  fof(f9,axiom,(
% 15.38/2.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f106,plain,(
% 15.38/2.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 15.38/2.49    inference(cnf_transformation,[],[f9])).
% 15.38/2.49  
% 15.38/2.49  fof(f8,axiom,(
% 15.38/2.49    ! [X0] : k2_subset_1(X0) = X0),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f105,plain,(
% 15.38/2.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 15.38/2.49    inference(cnf_transformation,[],[f8])).
% 15.38/2.49  
% 15.38/2.49  fof(f18,axiom,(
% 15.38/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f44,plain,(
% 15.38/2.49    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.38/2.49    inference(ennf_transformation,[],[f18])).
% 15.38/2.49  
% 15.38/2.49  fof(f117,plain,(
% 15.38/2.49    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.38/2.49    inference(cnf_transformation,[],[f44])).
% 15.38/2.49  
% 15.38/2.49  fof(f17,axiom,(
% 15.38/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f43,plain,(
% 15.38/2.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.38/2.49    inference(ennf_transformation,[],[f17])).
% 15.38/2.49  
% 15.38/2.49  fof(f115,plain,(
% 15.38/2.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.38/2.49    inference(cnf_transformation,[],[f43])).
% 15.38/2.49  
% 15.38/2.49  fof(f16,axiom,(
% 15.38/2.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f42,plain,(
% 15.38/2.49    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.38/2.49    inference(ennf_transformation,[],[f16])).
% 15.38/2.49  
% 15.38/2.49  fof(f114,plain,(
% 15.38/2.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.38/2.49    inference(cnf_transformation,[],[f42])).
% 15.38/2.49  
% 15.38/2.49  fof(f11,axiom,(
% 15.38/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f71,plain,(
% 15.38/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.38/2.49    inference(nnf_transformation,[],[f11])).
% 15.38/2.49  
% 15.38/2.49  fof(f108,plain,(
% 15.38/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.38/2.49    inference(cnf_transformation,[],[f71])).
% 15.38/2.49  
% 15.38/2.49  fof(f10,axiom,(
% 15.38/2.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f107,plain,(
% 15.38/2.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 15.38/2.49    inference(cnf_transformation,[],[f10])).
% 15.38/2.49  
% 15.38/2.49  fof(f29,conjecture,(
% 15.38/2.49    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f30,negated_conjecture,(
% 15.38/2.49    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 15.38/2.49    inference(negated_conjecture,[],[f29])).
% 15.38/2.49  
% 15.38/2.49  fof(f61,plain,(
% 15.38/2.49    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)))),
% 15.38/2.49    inference(ennf_transformation,[],[f30])).
% 15.38/2.49  
% 15.38/2.49  fof(f62,plain,(
% 15.38/2.49    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0))),
% 15.38/2.49    inference(flattening,[],[f61])).
% 15.38/2.49  
% 15.38/2.49  fof(f91,plain,(
% 15.38/2.49    ( ! [X0,X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~v5_pre_topc(sK7,X0,X1) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 15.38/2.49    introduced(choice_axiom,[])).
% 15.38/2.49  
% 15.38/2.49  fof(f90,plain,(
% 15.38/2.49    ( ! [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (~v5_pre_topc(X2,X0,sK6) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK6)) & v1_funct_1(X2)) & l1_pre_topc(sK6) & v2_pre_topc(sK6))) )),
% 15.38/2.49    introduced(choice_axiom,[])).
% 15.38/2.49  
% 15.38/2.49  fof(f89,plain,(
% 15.38/2.49    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v5_pre_topc(X2,sK5,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK5) & v1_tdlat_3(sK5) & v2_pre_topc(sK5))),
% 15.38/2.49    introduced(choice_axiom,[])).
% 15.38/2.49  
% 15.38/2.49  fof(f92,plain,(
% 15.38/2.49    ((~v5_pre_topc(sK7,sK5,sK6) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6)) & l1_pre_topc(sK5) & v1_tdlat_3(sK5) & v2_pre_topc(sK5)),
% 15.38/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f62,f91,f90,f89])).
% 15.38/2.49  
% 15.38/2.49  fof(f146,plain,(
% 15.38/2.49    l1_pre_topc(sK5)),
% 15.38/2.49    inference(cnf_transformation,[],[f92])).
% 15.38/2.49  
% 15.38/2.49  fof(f21,axiom,(
% 15.38/2.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f48,plain,(
% 15.38/2.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 15.38/2.49    inference(ennf_transformation,[],[f21])).
% 15.38/2.49  
% 15.38/2.49  fof(f121,plain,(
% 15.38/2.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 15.38/2.49    inference(cnf_transformation,[],[f48])).
% 15.38/2.49  
% 15.38/2.49  fof(f20,axiom,(
% 15.38/2.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f47,plain,(
% 15.38/2.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 15.38/2.49    inference(ennf_transformation,[],[f20])).
% 15.38/2.49  
% 15.38/2.49  fof(f120,plain,(
% 15.38/2.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 15.38/2.49    inference(cnf_transformation,[],[f47])).
% 15.38/2.49  
% 15.38/2.49  fof(f151,plain,(
% 15.38/2.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))),
% 15.38/2.49    inference(cnf_transformation,[],[f92])).
% 15.38/2.49  
% 15.38/2.49  fof(f148,plain,(
% 15.38/2.49    l1_pre_topc(sK6)),
% 15.38/2.49    inference(cnf_transformation,[],[f92])).
% 15.38/2.49  
% 15.38/2.49  fof(f23,axiom,(
% 15.38/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f51,plain,(
% 15.38/2.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.38/2.49    inference(ennf_transformation,[],[f23])).
% 15.38/2.49  
% 15.38/2.49  fof(f52,plain,(
% 15.38/2.49    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.38/2.49    inference(flattening,[],[f51])).
% 15.38/2.49  
% 15.38/2.49  fof(f73,plain,(
% 15.38/2.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.38/2.49    inference(nnf_transformation,[],[f52])).
% 15.38/2.49  
% 15.38/2.49  fof(f74,plain,(
% 15.38/2.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.38/2.49    inference(rectify,[],[f73])).
% 15.38/2.49  
% 15.38/2.49  fof(f75,plain,(
% 15.38/2.49    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0) & v3_pre_topc(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 15.38/2.49    introduced(choice_axiom,[])).
% 15.38/2.49  
% 15.38/2.49  fof(f76,plain,(
% 15.38/2.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0) & v3_pre_topc(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.38/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f74,f75])).
% 15.38/2.49  
% 15.38/2.49  fof(f126,plain,(
% 15.38/2.49    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 15.38/2.49    inference(cnf_transformation,[],[f76])).
% 15.38/2.49  
% 15.38/2.49  fof(f150,plain,(
% 15.38/2.49    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))),
% 15.38/2.49    inference(cnf_transformation,[],[f92])).
% 15.38/2.49  
% 15.38/2.49  fof(f149,plain,(
% 15.38/2.49    v1_funct_1(sK7)),
% 15.38/2.49    inference(cnf_transformation,[],[f92])).
% 15.38/2.49  
% 15.38/2.49  fof(f152,plain,(
% 15.38/2.49    ~v5_pre_topc(sK7,sK5,sK6)),
% 15.38/2.49    inference(cnf_transformation,[],[f92])).
% 15.38/2.49  
% 15.38/2.49  fof(f144,plain,(
% 15.38/2.49    v2_pre_topc(sK5)),
% 15.38/2.49    inference(cnf_transformation,[],[f92])).
% 15.38/2.49  
% 15.38/2.49  fof(f145,plain,(
% 15.38/2.49    v1_tdlat_3(sK5)),
% 15.38/2.49    inference(cnf_transformation,[],[f92])).
% 15.38/2.49  
% 15.38/2.49  fof(f130,plain,(
% 15.38/2.49    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 15.38/2.49    inference(cnf_transformation,[],[f76])).
% 15.38/2.49  
% 15.38/2.49  fof(f27,axiom,(
% 15.38/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f57,plain,(
% 15.38/2.49    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.38/2.49    inference(ennf_transformation,[],[f27])).
% 15.38/2.49  
% 15.38/2.49  fof(f58,plain,(
% 15.38/2.49    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.38/2.49    inference(flattening,[],[f57])).
% 15.38/2.49  
% 15.38/2.49  fof(f81,plain,(
% 15.38/2.49    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.38/2.49    inference(nnf_transformation,[],[f58])).
% 15.38/2.49  
% 15.38/2.49  fof(f82,plain,(
% 15.38/2.49    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.38/2.49    inference(rectify,[],[f81])).
% 15.38/2.49  
% 15.38/2.49  fof(f83,plain,(
% 15.38/2.49    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.38/2.49    introduced(choice_axiom,[])).
% 15.38/2.49  
% 15.38/2.49  fof(f84,plain,(
% 15.38/2.49    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.38/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f82,f83])).
% 15.38/2.49  
% 15.38/2.49  fof(f138,plain,(
% 15.38/2.49    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.38/2.49    inference(cnf_transformation,[],[f84])).
% 15.38/2.49  
% 15.38/2.49  fof(f4,axiom,(
% 15.38/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f67,plain,(
% 15.38/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.38/2.49    inference(nnf_transformation,[],[f4])).
% 15.38/2.49  
% 15.38/2.49  fof(f68,plain,(
% 15.38/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.38/2.49    inference(flattening,[],[f67])).
% 15.38/2.49  
% 15.38/2.49  fof(f99,plain,(
% 15.38/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.38/2.49    inference(cnf_transformation,[],[f68])).
% 15.38/2.49  
% 15.38/2.49  fof(f5,axiom,(
% 15.38/2.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f100,plain,(
% 15.38/2.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 15.38/2.49    inference(cnf_transformation,[],[f5])).
% 15.38/2.49  
% 15.38/2.49  fof(f24,axiom,(
% 15.38/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f53,plain,(
% 15.38/2.49    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.38/2.49    inference(ennf_transformation,[],[f24])).
% 15.38/2.49  
% 15.38/2.49  fof(f54,plain,(
% 15.38/2.49    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.38/2.49    inference(flattening,[],[f53])).
% 15.38/2.49  
% 15.38/2.49  fof(f77,plain,(
% 15.38/2.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.38/2.49    inference(nnf_transformation,[],[f54])).
% 15.38/2.49  
% 15.38/2.49  fof(f78,plain,(
% 15.38/2.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.38/2.49    inference(rectify,[],[f77])).
% 15.38/2.49  
% 15.38/2.49  fof(f79,plain,(
% 15.38/2.49    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2)))) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 15.38/2.49    introduced(choice_axiom,[])).
% 15.38/2.49  
% 15.38/2.49  fof(f80,plain,(
% 15.38/2.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2)))) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.38/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f78,f79])).
% 15.38/2.49  
% 15.38/2.49  fof(f133,plain,(
% 15.38/2.49    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.38/2.49    inference(cnf_transformation,[],[f80])).
% 15.38/2.49  
% 15.38/2.49  fof(f147,plain,(
% 15.38/2.49    v2_pre_topc(sK6)),
% 15.38/2.49    inference(cnf_transformation,[],[f92])).
% 15.38/2.49  
% 15.38/2.49  fof(f134,plain,(
% 15.38/2.49    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.38/2.49    inference(cnf_transformation,[],[f80])).
% 15.38/2.49  
% 15.38/2.49  fof(f28,axiom,(
% 15.38/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v4_pre_topc(X1,X0))))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f59,plain,(
% 15.38/2.49    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.38/2.49    inference(ennf_transformation,[],[f28])).
% 15.38/2.49  
% 15.38/2.49  fof(f60,plain,(
% 15.38/2.49    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.38/2.49    inference(flattening,[],[f59])).
% 15.38/2.49  
% 15.38/2.49  fof(f85,plain,(
% 15.38/2.49    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.38/2.49    inference(nnf_transformation,[],[f60])).
% 15.38/2.49  
% 15.38/2.49  fof(f86,plain,(
% 15.38/2.49    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.38/2.49    inference(rectify,[],[f85])).
% 15.38/2.49  
% 15.38/2.49  fof(f87,plain,(
% 15.38/2.49    ! [X0] : (? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.38/2.49    introduced(choice_axiom,[])).
% 15.38/2.49  
% 15.38/2.49  fof(f88,plain,(
% 15.38/2.49    ! [X0] : (((v1_tdlat_3(X0) | (~v4_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.38/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f86,f87])).
% 15.38/2.49  
% 15.38/2.49  fof(f141,plain,(
% 15.38/2.49    ( ! [X2,X0] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.38/2.49    inference(cnf_transformation,[],[f88])).
% 15.38/2.49  
% 15.38/2.49  fof(f22,axiom,(
% 15.38/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f49,plain,(
% 15.38/2.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.38/2.49    inference(ennf_transformation,[],[f22])).
% 15.38/2.49  
% 15.38/2.49  fof(f50,plain,(
% 15.38/2.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.38/2.49    inference(flattening,[],[f49])).
% 15.38/2.49  
% 15.38/2.49  fof(f122,plain,(
% 15.38/2.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.38/2.49    inference(cnf_transformation,[],[f50])).
% 15.38/2.49  
% 15.38/2.49  fof(f26,axiom,(
% 15.38/2.49    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 15.38/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.49  
% 15.38/2.49  fof(f55,plain,(
% 15.38/2.49    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 15.38/2.49    inference(ennf_transformation,[],[f26])).
% 15.38/2.49  
% 15.38/2.49  fof(f56,plain,(
% 15.38/2.49    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 15.38/2.49    inference(flattening,[],[f55])).
% 15.38/2.49  
% 15.38/2.49  fof(f137,plain,(
% 15.38/2.49    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 15.38/2.49    inference(cnf_transformation,[],[f56])).
% 15.38/2.49  
% 15.38/2.49  cnf(c_9,plain,
% 15.38/2.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.38/2.49      inference(cnf_transformation,[],[f155]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_13,plain,
% 15.38/2.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 15.38/2.49      inference(cnf_transformation,[],[f106]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5237,plain,
% 15.38/2.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_12,plain,
% 15.38/2.49      ( k2_subset_1(X0) = X0 ),
% 15.38/2.49      inference(cnf_transformation,[],[f105]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5270,plain,
% 15.38/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.38/2.49      inference(light_normalisation,[status(thm)],[c_5237,c_12]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_23,plain,
% 15.38/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.38/2.49      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 15.38/2.49      inference(cnf_transformation,[],[f117]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5231,plain,
% 15.38/2.49      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 15.38/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_11456,plain,
% 15.38/2.49      ( k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1) = k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_5270,c_5231]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_22,plain,
% 15.38/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.38/2.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.38/2.49      inference(cnf_transformation,[],[f115]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5232,plain,
% 15.38/2.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.38/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_10015,plain,
% 15.38/2.49      ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_5270,c_5232]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_46889,plain,
% 15.38/2.49      ( k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.38/2.49      inference(light_normalisation,[status(thm)],[c_11456,c_10015]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_46892,plain,
% 15.38/2.49      ( k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_9,c_46889]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_46920,plain,
% 15.38/2.49      ( k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 15.38/2.49      inference(light_normalisation,[status(thm)],[c_46892,c_9]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_21,plain,
% 15.38/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.38/2.49      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 15.38/2.49      inference(cnf_transformation,[],[f114]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5233,plain,
% 15.38/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.38/2.49      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_16,plain,
% 15.38/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.38/2.49      inference(cnf_transformation,[],[f108]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5234,plain,
% 15.38/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.38/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_12800,plain,
% 15.38/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.38/2.49      | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1) = iProver_top ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_5233,c_5234]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_59528,plain,
% 15.38/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top
% 15.38/2.49      | r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_46920,c_12800]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_59668,plain,
% 15.38/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.38/2.49      | r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 15.38/2.49      inference(light_normalisation,[status(thm)],[c_59528,c_9]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_14,plain,
% 15.38/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 15.38/2.49      inference(cnf_transformation,[],[f107]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_177,plain,
% 15.38/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_179,plain,
% 15.38/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.38/2.49      inference(instantiation,[status(thm)],[c_177]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_59725,plain,
% 15.38/2.49      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 15.38/2.49      inference(global_propositional_subsumption,[status(thm)],[c_59668,c_179]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_57,negated_conjecture,
% 15.38/2.49      ( l1_pre_topc(sK5) ),
% 15.38/2.49      inference(cnf_transformation,[],[f146]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5219,plain,
% 15.38/2.49      ( l1_pre_topc(sK5) = iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_28,plain,
% 15.38/2.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 15.38/2.49      inference(cnf_transformation,[],[f121]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_27,plain,
% 15.38/2.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 15.38/2.49      inference(cnf_transformation,[],[f120]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_723,plain,
% 15.38/2.49      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 15.38/2.49      inference(resolution,[status(thm)],[c_28,c_27]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5216,plain,
% 15.38/2.49      ( u1_struct_0(X0) = k2_struct_0(X0) | l1_pre_topc(X0) != iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_10857,plain,
% 15.38/2.49      ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_5219,c_5216]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_52,negated_conjecture,
% 15.38/2.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
% 15.38/2.49      inference(cnf_transformation,[],[f151]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5222,plain,
% 15.38/2.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_8511,plain,
% 15.38/2.49      ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))) = iProver_top ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_5222,c_5234]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_11496,plain,
% 15.38/2.49      ( r1_tarski(sK7,k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK6))) = iProver_top ),
% 15.38/2.49      inference(demodulation,[status(thm)],[c_10857,c_8511]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_55,negated_conjecture,
% 15.38/2.49      ( l1_pre_topc(sK6) ),
% 15.38/2.49      inference(cnf_transformation,[],[f148]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5221,plain,
% 15.38/2.49      ( l1_pre_topc(sK6) = iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_10856,plain,
% 15.38/2.49      ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_5221,c_5216]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_36,plain,
% 15.38/2.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.38/2.49      | v5_pre_topc(X0,X1,X2)
% 15.38/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.38/2.49      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 15.38/2.49      | ~ v1_funct_1(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X2)
% 15.38/2.49      | k2_struct_0(X2) = k1_xboole_0 ),
% 15.38/2.49      inference(cnf_transformation,[],[f126]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_53,negated_conjecture,
% 15.38/2.49      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
% 15.38/2.49      inference(cnf_transformation,[],[f150]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1389,plain,
% 15.38/2.49      ( v5_pre_topc(X0,X1,X2)
% 15.38/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.38/2.49      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 15.38/2.49      | ~ v1_funct_1(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X2)
% 15.38/2.49      | u1_struct_0(X2) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK5)
% 15.38/2.49      | k2_struct_0(X2) = k1_xboole_0
% 15.38/2.49      | sK7 != X0 ),
% 15.38/2.49      inference(resolution_lifted,[status(thm)],[c_36,c_53]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1390,plain,
% 15.38/2.49      ( v5_pre_topc(sK7,X0,X1)
% 15.38/2.49      | m1_subset_1(sK1(X0,X1,sK7),k1_zfmisc_1(u1_struct_0(X1)))
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | ~ v1_funct_1(sK7)
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5)
% 15.38/2.49      | k2_struct_0(X1) = k1_xboole_0 ),
% 15.38/2.49      inference(unflattening,[status(thm)],[c_1389]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_54,negated_conjecture,
% 15.38/2.49      ( v1_funct_1(sK7) ),
% 15.38/2.49      inference(cnf_transformation,[],[f149]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1394,plain,
% 15.38/2.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | m1_subset_1(sK1(X0,X1,sK7),k1_zfmisc_1(u1_struct_0(X1)))
% 15.38/2.49      | v5_pre_topc(sK7,X0,X1)
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5)
% 15.38/2.49      | k2_struct_0(X1) = k1_xboole_0 ),
% 15.38/2.49      inference(global_propositional_subsumption,[status(thm)],[c_1390,c_54]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1395,plain,
% 15.38/2.49      ( v5_pre_topc(sK7,X0,X1)
% 15.38/2.49      | m1_subset_1(sK1(X0,X1,sK7),k1_zfmisc_1(u1_struct_0(X1)))
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5)
% 15.38/2.49      | k2_struct_0(X1) = k1_xboole_0 ),
% 15.38/2.49      inference(renaming,[status(thm)],[c_1394]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5206,plain,
% 15.38/2.49      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK5)
% 15.38/2.49      | k2_struct_0(X0) = k1_xboole_0
% 15.38/2.49      | v5_pre_topc(sK7,X1,X0) = iProver_top
% 15.38/2.49      | m1_subset_1(sK1(X1,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | l1_pre_topc(X0) != iProver_top
% 15.38/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_1395]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_6679,plain,
% 15.38/2.49      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | k2_struct_0(X0) = k1_xboole_0
% 15.38/2.49      | v5_pre_topc(sK7,sK5,X0) = iProver_top
% 15.38/2.49      | m1_subset_1(sK1(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | l1_pre_topc(X0) != iProver_top
% 15.38/2.49      | l1_pre_topc(sK5) != iProver_top ),
% 15.38/2.49      inference(equality_resolution,[status(thm)],[c_5206]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_62,plain,
% 15.38/2.49      ( l1_pre_topc(sK5) = iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_4159,plain,( X0 = X0 ),theory(equality) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_6041,plain,
% 15.38/2.49      ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
% 15.38/2.49      inference(instantiation,[status(thm)],[c_4159]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_6046,plain,
% 15.38/2.49      ( v5_pre_topc(sK7,sK5,X0)
% 15.38/2.49      | m1_subset_1(sK1(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(sK5)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 15.38/2.49      | k2_struct_0(X0) = k1_xboole_0 ),
% 15.38/2.49      inference(instantiation,[status(thm)],[c_1395]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_6047,plain,
% 15.38/2.49      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 15.38/2.49      | k2_struct_0(X0) = k1_xboole_0
% 15.38/2.49      | v5_pre_topc(sK7,sK5,X0) = iProver_top
% 15.38/2.49      | m1_subset_1(sK1(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | l1_pre_topc(X0) != iProver_top
% 15.38/2.49      | l1_pre_topc(sK5) != iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_6046]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_8047,plain,
% 15.38/2.49      ( l1_pre_topc(X0) != iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | m1_subset_1(sK1(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.38/2.49      | v5_pre_topc(sK7,sK5,X0) = iProver_top
% 15.38/2.49      | k2_struct_0(X0) = k1_xboole_0
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 15.38/2.49      inference(global_propositional_subsumption,
% 15.38/2.49                [status(thm)],
% 15.38/2.49                [c_6679,c_62,c_6041,c_6047]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_8048,plain,
% 15.38/2.49      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | k2_struct_0(X0) = k1_xboole_0
% 15.38/2.49      | v5_pre_topc(sK7,sK5,X0) = iProver_top
% 15.38/2.49      | m1_subset_1(sK1(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.38/2.49      inference(renaming,[status(thm)],[c_8047]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_8059,plain,
% 15.38/2.49      ( k2_struct_0(sK6) = k1_xboole_0
% 15.38/2.49      | v5_pre_topc(sK7,sK5,sK6) = iProver_top
% 15.38/2.49      | m1_subset_1(sK1(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
% 15.38/2.49      | l1_pre_topc(sK6) != iProver_top ),
% 15.38/2.49      inference(equality_resolution,[status(thm)],[c_8048]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_64,plain,
% 15.38/2.49      ( l1_pre_topc(sK6) = iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_67,plain,
% 15.38/2.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_51,negated_conjecture,
% 15.38/2.49      ( ~ v5_pre_topc(sK7,sK5,sK6) ),
% 15.38/2.49      inference(cnf_transformation,[],[f152]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_68,plain,
% 15.38/2.49      ( v5_pre_topc(sK7,sK5,sK6) != iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_8956,plain,
% 15.38/2.49      ( k2_struct_0(sK6) = k1_xboole_0
% 15.38/2.49      | m1_subset_1(sK1(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 15.38/2.49      inference(global_propositional_subsumption,
% 15.38/2.49                [status(thm)],
% 15.38/2.49                [c_8059,c_64,c_67,c_68]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_8962,plain,
% 15.38/2.49      ( k2_struct_0(sK6) = k1_xboole_0
% 15.38/2.49      | r1_tarski(sK1(sK5,sK6,sK7),u1_struct_0(sK6)) = iProver_top ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_8956,c_5234]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_59,negated_conjecture,
% 15.38/2.49      ( v2_pre_topc(sK5) ),
% 15.38/2.49      inference(cnf_transformation,[],[f144]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_58,negated_conjecture,
% 15.38/2.49      ( v1_tdlat_3(sK5) ),
% 15.38/2.49      inference(cnf_transformation,[],[f145]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_32,plain,
% 15.38/2.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.38/2.49      | v5_pre_topc(X0,X1,X2)
% 15.38/2.49      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X1)
% 15.38/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.38/2.49      | ~ v1_funct_1(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X2)
% 15.38/2.49      | k2_struct_0(X2) = k1_xboole_0 ),
% 15.38/2.49      inference(cnf_transformation,[],[f130]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1533,plain,
% 15.38/2.49      ( v5_pre_topc(X0,X1,X2)
% 15.38/2.49      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)),X1)
% 15.38/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.38/2.49      | ~ v1_funct_1(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X2)
% 15.38/2.49      | u1_struct_0(X2) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK5)
% 15.38/2.49      | k2_struct_0(X2) = k1_xboole_0
% 15.38/2.49      | sK7 != X0 ),
% 15.38/2.49      inference(resolution_lifted,[status(thm)],[c_32,c_53]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1534,plain,
% 15.38/2.49      ( v5_pre_topc(sK7,X0,X1)
% 15.38/2.49      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK1(X0,X1,sK7)),X0)
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | ~ v1_funct_1(sK7)
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5)
% 15.38/2.49      | k2_struct_0(X1) = k1_xboole_0 ),
% 15.38/2.49      inference(unflattening,[status(thm)],[c_1533]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1538,plain,
% 15.38/2.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK1(X0,X1,sK7)),X0)
% 15.38/2.49      | v5_pre_topc(sK7,X0,X1)
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5)
% 15.38/2.49      | k2_struct_0(X1) = k1_xboole_0 ),
% 15.38/2.49      inference(global_propositional_subsumption,[status(thm)],[c_1534,c_54]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1539,plain,
% 15.38/2.49      ( v5_pre_topc(sK7,X0,X1)
% 15.38/2.49      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK1(X0,X1,sK7)),X0)
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5)
% 15.38/2.49      | k2_struct_0(X1) = k1_xboole_0 ),
% 15.38/2.49      inference(renaming,[status(thm)],[c_1538]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_2410,plain,
% 15.38/2.49      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK1(X0,X1,sK7)),X0)
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5)
% 15.38/2.49      | k2_struct_0(X1) = k1_xboole_0
% 15.38/2.49      | sK6 != X1
% 15.38/2.49      | sK5 != X0
% 15.38/2.49      | sK7 != sK7 ),
% 15.38/2.49      inference(resolution_lifted,[status(thm)],[c_51,c_1539]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_2411,plain,
% 15.38/2.49      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
% 15.38/2.49      | ~ l1_pre_topc(sK6)
% 15.38/2.49      | ~ l1_pre_topc(sK5)
% 15.38/2.49      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 15.38/2.49      | k2_struct_0(sK6) = k1_xboole_0 ),
% 15.38/2.49      inference(unflattening,[status(thm)],[c_2410]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_2413,plain,
% 15.38/2.49      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
% 15.38/2.49      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 15.38/2.49      | k2_struct_0(sK6) = k1_xboole_0 ),
% 15.38/2.49      inference(global_propositional_subsumption,
% 15.38/2.49                [status(thm)],
% 15.38/2.49                [c_2411,c_57,c_55,c_52]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_7391,plain,
% 15.38/2.49      ( u1_struct_0(sK6) = u1_struct_0(sK6) ),
% 15.38/2.49      inference(instantiation,[status(thm)],[c_4159]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_47,plain,
% 15.38/2.49      ( v3_pre_topc(X0,X1)
% 15.38/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.38/2.49      | ~ v1_tdlat_3(X1)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X1) ),
% 15.38/2.49      inference(cnf_transformation,[],[f138]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5965,plain,
% 15.38/2.49      ( v3_pre_topc(X0,sK5)
% 15.38/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 15.38/2.49      | ~ v1_tdlat_3(sK5)
% 15.38/2.49      | ~ v2_pre_topc(sK5)
% 15.38/2.49      | ~ l1_pre_topc(sK5) ),
% 15.38/2.49      inference(instantiation,[status(thm)],[c_47]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_6417,plain,
% 15.38/2.49      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK5),X0,X1,X2),sK5)
% 15.38/2.49      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK5),X0,X1,X2),k1_zfmisc_1(u1_struct_0(sK5)))
% 15.38/2.49      | ~ v1_tdlat_3(sK5)
% 15.38/2.49      | ~ v2_pre_topc(sK5)
% 15.38/2.49      | ~ l1_pre_topc(sK5) ),
% 15.38/2.49      inference(instantiation,[status(thm)],[c_5965]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_6974,plain,
% 15.38/2.49      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,X0),sK5)
% 15.38/2.49      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 15.38/2.49      | ~ v1_tdlat_3(sK5)
% 15.38/2.49      | ~ v2_pre_topc(sK5)
% 15.38/2.49      | ~ l1_pre_topc(sK5) ),
% 15.38/2.49      inference(instantiation,[status(thm)],[c_6417]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_7751,plain,
% 15.38/2.49      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),sK5)
% 15.38/2.49      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 15.38/2.49      | ~ v1_tdlat_3(sK5)
% 15.38/2.49      | ~ v2_pre_topc(sK5)
% 15.38/2.49      | ~ l1_pre_topc(sK5) ),
% 15.38/2.49      inference(instantiation,[status(thm)],[c_6974]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5981,plain,
% 15.38/2.49      ( m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
% 15.38/2.49      inference(instantiation,[status(thm)],[c_21]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_9922,plain,
% 15.38/2.49      ( m1_subset_1(k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK1(sK5,sK6,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
% 15.38/2.49      inference(instantiation,[status(thm)],[c_5981]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_10518,plain,
% 15.38/2.49      ( k2_struct_0(sK6) = k1_xboole_0 ),
% 15.38/2.49      inference(global_propositional_subsumption,
% 15.38/2.49                [status(thm)],
% 15.38/2.49                [c_8962,c_59,c_58,c_57,c_52,c_2413,c_6041,c_7391,c_7751,c_9922]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_10861,plain,
% 15.38/2.49      ( u1_struct_0(sK6) = k1_xboole_0 ),
% 15.38/2.49      inference(light_normalisation,[status(thm)],[c_10856,c_10518]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_12283,plain,
% 15.38/2.49      ( r1_tarski(sK7,k2_zfmisc_1(k2_struct_0(sK5),k1_xboole_0)) = iProver_top ),
% 15.38/2.49      inference(light_normalisation,[status(thm)],[c_11496,c_10861]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_12284,plain,
% 15.38/2.49      ( r1_tarski(sK7,k1_xboole_0) = iProver_top ),
% 15.38/2.49      inference(demodulation,[status(thm)],[c_12283,c_9]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_4,plain,
% 15.38/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.38/2.49      inference(cnf_transformation,[],[f99]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5241,plain,
% 15.38/2.49      ( X0 = X1
% 15.38/2.49      | r1_tarski(X0,X1) != iProver_top
% 15.38/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_12287,plain,
% 15.38/2.49      ( sK7 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK7) != iProver_top ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_12284,c_5241]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_12288,plain,
% 15.38/2.49      ( ~ r1_tarski(k1_xboole_0,sK7) | sK7 = k1_xboole_0 ),
% 15.38/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_12287]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_7,plain,
% 15.38/2.49      ( r1_tarski(k1_xboole_0,X0) ),
% 15.38/2.49      inference(cnf_transformation,[],[f100]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_22610,plain,
% 15.38/2.49      ( r1_tarski(k1_xboole_0,sK7) ),
% 15.38/2.49      inference(instantiation,[status(thm)],[c_7]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_49597,plain,
% 15.38/2.49      ( sK7 = k1_xboole_0 ),
% 15.38/2.49      inference(global_propositional_subsumption,
% 15.38/2.49                [status(thm)],
% 15.38/2.49                [c_12287,c_12288,c_22610]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_40,plain,
% 15.38/2.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.38/2.49      | v5_pre_topc(X0,X1,X2)
% 15.38/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.38/2.49      | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 15.38/2.49      | ~ v1_funct_1(X0)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ v2_pre_topc(X2)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X2) ),
% 15.38/2.49      inference(cnf_transformation,[],[f133]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1227,plain,
% 15.38/2.49      ( v5_pre_topc(X0,X1,X2)
% 15.38/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.38/2.49      | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 15.38/2.49      | ~ v1_funct_1(X0)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ v2_pre_topc(X2)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X2)
% 15.38/2.49      | u1_struct_0(X2) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK5)
% 15.38/2.49      | sK7 != X0 ),
% 15.38/2.49      inference(resolution_lifted,[status(thm)],[c_40,c_53]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1228,plain,
% 15.38/2.49      ( v5_pre_topc(sK7,X0,X1)
% 15.38/2.49      | m1_subset_1(sK2(X0,X1,sK7),k1_zfmisc_1(u1_struct_0(X1)))
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | ~ v1_funct_1(sK7)
% 15.38/2.49      | ~ v2_pre_topc(X0)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5) ),
% 15.38/2.49      inference(unflattening,[status(thm)],[c_1227]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1232,plain,
% 15.38/2.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | m1_subset_1(sK2(X0,X1,sK7),k1_zfmisc_1(u1_struct_0(X1)))
% 15.38/2.49      | v5_pre_topc(sK7,X0,X1)
% 15.38/2.49      | ~ v2_pre_topc(X0)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5) ),
% 15.38/2.49      inference(global_propositional_subsumption,[status(thm)],[c_1228,c_54]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1233,plain,
% 15.38/2.49      ( v5_pre_topc(sK7,X0,X1)
% 15.38/2.49      | m1_subset_1(sK2(X0,X1,sK7),k1_zfmisc_1(u1_struct_0(X1)))
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | ~ v2_pre_topc(X0)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5) ),
% 15.38/2.49      inference(renaming,[status(thm)],[c_1232]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5210,plain,
% 15.38/2.49      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK5)
% 15.38/2.49      | v5_pre_topc(sK7,X1,X0) = iProver_top
% 15.38/2.49      | m1_subset_1(sK2(X1,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | v2_pre_topc(X0) != iProver_top
% 15.38/2.49      | v2_pre_topc(X1) != iProver_top
% 15.38/2.49      | l1_pre_topc(X0) != iProver_top
% 15.38/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_1233]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_7270,plain,
% 15.38/2.49      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | v5_pre_topc(sK7,sK5,X0) = iProver_top
% 15.38/2.49      | m1_subset_1(sK2(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | v2_pre_topc(X0) != iProver_top
% 15.38/2.49      | v2_pre_topc(sK5) != iProver_top
% 15.38/2.49      | l1_pre_topc(X0) != iProver_top
% 15.38/2.49      | l1_pre_topc(sK5) != iProver_top ),
% 15.38/2.49      inference(equality_resolution,[status(thm)],[c_5210]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_60,plain,
% 15.38/2.49      ( v2_pre_topc(sK5) = iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_6044,plain,
% 15.38/2.49      ( v5_pre_topc(sK7,sK5,X0)
% 15.38/2.49      | m1_subset_1(sK2(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 15.38/2.49      | ~ v2_pre_topc(X0)
% 15.38/2.49      | ~ v2_pre_topc(sK5)
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(sK5)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 15.38/2.49      inference(instantiation,[status(thm)],[c_1233]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_6055,plain,
% 15.38/2.49      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 15.38/2.49      | v5_pre_topc(sK7,sK5,X0) = iProver_top
% 15.38/2.49      | m1_subset_1(sK2(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | v2_pre_topc(X0) != iProver_top
% 15.38/2.49      | v2_pre_topc(sK5) != iProver_top
% 15.38/2.49      | l1_pre_topc(X0) != iProver_top
% 15.38/2.49      | l1_pre_topc(sK5) != iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_6044]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_8141,plain,
% 15.38/2.49      ( l1_pre_topc(X0) != iProver_top
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | v5_pre_topc(sK7,sK5,X0) = iProver_top
% 15.38/2.49      | m1_subset_1(sK2(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | v2_pre_topc(X0) != iProver_top ),
% 15.38/2.49      inference(global_propositional_subsumption,
% 15.38/2.49                [status(thm)],
% 15.38/2.49                [c_7270,c_60,c_62,c_6041,c_6055]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_8142,plain,
% 15.38/2.49      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | v5_pre_topc(sK7,sK5,X0) = iProver_top
% 15.38/2.49      | m1_subset_1(sK2(sK5,X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | v2_pre_topc(X0) != iProver_top
% 15.38/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.38/2.49      inference(renaming,[status(thm)],[c_8141]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_8153,plain,
% 15.38/2.49      ( v5_pre_topc(sK7,sK5,sK6) = iProver_top
% 15.38/2.49      | m1_subset_1(sK2(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
% 15.38/2.49      | v2_pre_topc(sK6) != iProver_top
% 15.38/2.49      | l1_pre_topc(sK6) != iProver_top ),
% 15.38/2.49      inference(equality_resolution,[status(thm)],[c_8142]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_56,negated_conjecture,
% 15.38/2.49      ( v2_pre_topc(sK6) ),
% 15.38/2.49      inference(cnf_transformation,[],[f147]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_63,plain,
% 15.38/2.49      ( v2_pre_topc(sK6) = iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_2527,plain,
% 15.38/2.49      ( m1_subset_1(sK2(X0,X1,sK7),k1_zfmisc_1(u1_struct_0(X1)))
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | ~ v2_pre_topc(X0)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5)
% 15.38/2.49      | sK6 != X1
% 15.38/2.49      | sK5 != X0
% 15.38/2.49      | sK7 != sK7 ),
% 15.38/2.49      inference(resolution_lifted,[status(thm)],[c_51,c_1233]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_2528,plain,
% 15.38/2.49      ( m1_subset_1(sK2(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
% 15.38/2.49      | ~ v2_pre_topc(sK6)
% 15.38/2.49      | ~ v2_pre_topc(sK5)
% 15.38/2.49      | ~ l1_pre_topc(sK6)
% 15.38/2.49      | ~ l1_pre_topc(sK5)
% 15.38/2.49      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 15.38/2.49      inference(unflattening,[status(thm)],[c_2527]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_2529,plain,
% 15.38/2.49      ( u1_struct_0(sK6) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 15.38/2.49      | m1_subset_1(sK2(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
% 15.38/2.49      | v2_pre_topc(sK6) != iProver_top
% 15.38/2.49      | v2_pre_topc(sK5) != iProver_top
% 15.38/2.49      | l1_pre_topc(sK6) != iProver_top
% 15.38/2.49      | l1_pre_topc(sK5) != iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_2528]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_9287,plain,
% 15.38/2.49      ( m1_subset_1(sK2(sK5,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 15.38/2.49      inference(global_propositional_subsumption,
% 15.38/2.49                [status(thm)],
% 15.38/2.49                [c_8153,c_60,c_62,c_63,c_64,c_67,c_2529,c_6041,c_7391]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_9292,plain,
% 15.38/2.49      ( r1_tarski(sK2(sK5,sK6,sK7),u1_struct_0(sK6)) = iProver_top ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_9287,c_5234]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_10276,plain,
% 15.38/2.49      ( sK2(sK5,sK6,sK7) = u1_struct_0(sK6)
% 15.38/2.49      | r1_tarski(u1_struct_0(sK6),sK2(sK5,sK6,sK7)) != iProver_top ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_9292,c_5241]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_12131,plain,
% 15.38/2.49      ( sK2(sK5,sK6,sK7) = k1_xboole_0
% 15.38/2.49      | r1_tarski(k1_xboole_0,sK2(sK5,sK6,sK7)) != iProver_top ),
% 15.38/2.49      inference(demodulation,[status(thm)],[c_10861,c_10276]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5239,plain,
% 15.38/2.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_20361,plain,
% 15.38/2.49      ( sK2(sK5,sK6,sK7) = k1_xboole_0 ),
% 15.38/2.49      inference(forward_subsumption_resolution,[status(thm)],[c_12131,c_5239]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_39,plain,
% 15.38/2.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.38/2.49      | v5_pre_topc(X0,X1,X2)
% 15.38/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.38/2.49      | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK2(X1,X2,X0))))
% 15.38/2.49      | ~ v1_funct_1(X0)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ v2_pre_topc(X2)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X2) ),
% 15.38/2.49      inference(cnf_transformation,[],[f134]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1266,plain,
% 15.38/2.49      ( v5_pre_topc(X0,X1,X2)
% 15.38/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.38/2.49      | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK2(X1,X2,X0))))
% 15.38/2.49      | ~ v1_funct_1(X0)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ v2_pre_topc(X2)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X2)
% 15.38/2.49      | u1_struct_0(X2) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK5)
% 15.38/2.49      | sK7 != X0 ),
% 15.38/2.49      inference(resolution_lifted,[status(thm)],[c_39,c_53]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1267,plain,
% 15.38/2.49      ( v5_pre_topc(sK7,X0,X1)
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK2(X0,X1,sK7))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,k2_pre_topc(X1,sK2(X0,X1,sK7))))
% 15.38/2.49      | ~ v1_funct_1(sK7)
% 15.38/2.49      | ~ v2_pre_topc(X0)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5) ),
% 15.38/2.49      inference(unflattening,[status(thm)],[c_1266]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1271,plain,
% 15.38/2.49      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK2(X0,X1,sK7))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,k2_pre_topc(X1,sK2(X0,X1,sK7))))
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | v5_pre_topc(sK7,X0,X1)
% 15.38/2.49      | ~ v2_pre_topc(X0)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5) ),
% 15.38/2.49      inference(global_propositional_subsumption,[status(thm)],[c_1267,c_54]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_1272,plain,
% 15.38/2.49      ( v5_pre_topc(sK7,X0,X1)
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK2(X0,X1,sK7))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,k2_pre_topc(X1,sK2(X0,X1,sK7))))
% 15.38/2.49      | ~ v2_pre_topc(X0)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5) ),
% 15.38/2.49      inference(renaming,[status(thm)],[c_1271]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5209,plain,
% 15.38/2.49      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK5)
% 15.38/2.49      | v5_pre_topc(sK7,X1,X0) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK7,sK2(X1,X0,sK7))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK7,k2_pre_topc(X0,sK2(X1,X0,sK7)))) != iProver_top
% 15.38/2.49      | v2_pre_topc(X0) != iProver_top
% 15.38/2.49      | v2_pre_topc(X1) != iProver_top
% 15.38/2.49      | l1_pre_topc(X0) != iProver_top
% 15.38/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_1272]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_6320,plain,
% 15.38/2.49      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | v5_pre_topc(sK7,sK5,X0) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,sK2(sK5,X0,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,k2_pre_topc(X0,sK2(sK5,X0,sK7)))) != iProver_top
% 15.38/2.49      | v2_pre_topc(X0) != iProver_top
% 15.38/2.49      | v2_pre_topc(sK5) != iProver_top
% 15.38/2.49      | l1_pre_topc(X0) != iProver_top
% 15.38/2.49      | l1_pre_topc(sK5) != iProver_top ),
% 15.38/2.49      inference(equality_resolution,[status(thm)],[c_5209]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_6042,plain,
% 15.38/2.49      ( v5_pre_topc(sK7,sK5,X0)
% 15.38/2.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 15.38/2.49      | ~ r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,sK2(sK5,X0,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,k2_pre_topc(X0,sK2(sK5,X0,sK7))))
% 15.38/2.49      | ~ v2_pre_topc(X0)
% 15.38/2.49      | ~ v2_pre_topc(sK5)
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(sK5)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 15.38/2.49      inference(instantiation,[status(thm)],[c_1272]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_6063,plain,
% 15.38/2.49      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 15.38/2.49      | v5_pre_topc(sK7,sK5,X0) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,sK2(sK5,X0,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,k2_pre_topc(X0,sK2(sK5,X0,sK7)))) != iProver_top
% 15.38/2.49      | v2_pre_topc(X0) != iProver_top
% 15.38/2.49      | v2_pre_topc(sK5) != iProver_top
% 15.38/2.49      | l1_pre_topc(X0) != iProver_top
% 15.38/2.49      | l1_pre_topc(sK5) != iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_6042]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_7538,plain,
% 15.38/2.49      ( l1_pre_topc(X0) != iProver_top
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | v5_pre_topc(sK7,sK5,X0) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,sK2(sK5,X0,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,k2_pre_topc(X0,sK2(sK5,X0,sK7)))) != iProver_top
% 15.38/2.49      | v2_pre_topc(X0) != iProver_top ),
% 15.38/2.49      inference(global_propositional_subsumption,
% 15.38/2.49                [status(thm)],
% 15.38/2.49                [c_6320,c_60,c_62,c_6041,c_6063]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_7539,plain,
% 15.38/2.49      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 15.38/2.49      | v5_pre_topc(sK7,sK5,X0) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
% 15.38/2.49      | r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,sK2(sK5,X0,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(X0),sK7,k2_pre_topc(X0,sK2(sK5,X0,sK7)))) != iProver_top
% 15.38/2.49      | v2_pre_topc(X0) != iProver_top
% 15.38/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.38/2.49      inference(renaming,[status(thm)],[c_7538]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_7550,plain,
% 15.38/2.49      ( v5_pre_topc(sK7,sK5,sK6) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
% 15.38/2.49      | r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK2(sK5,sK6,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,k2_pre_topc(sK6,sK2(sK5,sK6,sK7)))) != iProver_top
% 15.38/2.49      | v2_pre_topc(sK6) != iProver_top
% 15.38/2.49      | l1_pre_topc(sK6) != iProver_top ),
% 15.38/2.49      inference(equality_resolution,[status(thm)],[c_7539]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_2510,plain,
% 15.38/2.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.38/2.49      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,sK2(X0,X1,sK7))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK7,k2_pre_topc(X1,sK2(X0,X1,sK7))))
% 15.38/2.49      | ~ v2_pre_topc(X0)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X0)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(X0) != u1_struct_0(sK5)
% 15.38/2.49      | sK6 != X1
% 15.38/2.49      | sK5 != X0
% 15.38/2.49      | sK7 != sK7 ),
% 15.38/2.49      inference(resolution_lifted,[status(thm)],[c_51,c_1272]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_2511,plain,
% 15.38/2.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
% 15.38/2.49      | ~ r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK2(sK5,sK6,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,k2_pre_topc(sK6,sK2(sK5,sK6,sK7))))
% 15.38/2.49      | ~ v2_pre_topc(sK6)
% 15.38/2.49      | ~ v2_pre_topc(sK5)
% 15.38/2.49      | ~ l1_pre_topc(sK6)
% 15.38/2.49      | ~ l1_pre_topc(sK5)
% 15.38/2.49      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 15.38/2.49      inference(unflattening,[status(thm)],[c_2510]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_2512,plain,
% 15.38/2.49      ( u1_struct_0(sK6) != u1_struct_0(sK6)
% 15.38/2.49      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
% 15.38/2.49      | r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK2(sK5,sK6,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,k2_pre_topc(sK6,sK2(sK5,sK6,sK7)))) != iProver_top
% 15.38/2.49      | v2_pre_topc(sK6) != iProver_top
% 15.38/2.49      | v2_pre_topc(sK5) != iProver_top
% 15.38/2.49      | l1_pre_topc(sK6) != iProver_top
% 15.38/2.49      | l1_pre_topc(sK5) != iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_2511]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_8403,plain,
% 15.38/2.49      ( r1_tarski(k2_pre_topc(sK5,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,sK2(sK5,sK6,sK7))),k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,k2_pre_topc(sK6,sK2(sK5,sK6,sK7)))) != iProver_top ),
% 15.38/2.49      inference(global_propositional_subsumption,
% 15.38/2.49                [status(thm)],
% 15.38/2.49                [c_7550,c_60,c_62,c_63,c_64,c_67,c_2512,c_6041,c_7391]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_11497,plain,
% 15.38/2.49      ( r1_tarski(k2_pre_topc(sK5,k8_relset_1(k2_struct_0(sK5),u1_struct_0(sK6),sK7,sK2(sK5,sK6,sK7))),k8_relset_1(k2_struct_0(sK5),u1_struct_0(sK6),sK7,k2_pre_topc(sK6,sK2(sK5,sK6,sK7)))) != iProver_top ),
% 15.38/2.49      inference(demodulation,[status(thm)],[c_10857,c_8403]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_13247,plain,
% 15.38/2.49      ( r1_tarski(k2_pre_topc(sK5,k8_relset_1(k2_struct_0(sK5),k1_xboole_0,sK7,sK2(sK5,sK6,sK7))),k8_relset_1(k2_struct_0(sK5),k1_xboole_0,sK7,k2_pre_topc(sK6,sK2(sK5,sK6,sK7)))) != iProver_top ),
% 15.38/2.49      inference(light_normalisation,[status(thm)],[c_11497,c_10861]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_20364,plain,
% 15.38/2.49      ( r1_tarski(k2_pre_topc(sK5,k8_relset_1(k2_struct_0(sK5),k1_xboole_0,sK7,k1_xboole_0)),k8_relset_1(k2_struct_0(sK5),k1_xboole_0,sK7,k2_pre_topc(sK6,k1_xboole_0))) != iProver_top ),
% 15.38/2.49      inference(demodulation,[status(thm)],[c_20361,c_13247]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_11454,plain,
% 15.38/2.49      ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,u1_struct_0(sK6)) = k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7) ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_5222,c_5231]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_10013,plain,
% 15.38/2.49      ( k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7) = k1_relat_1(sK7) ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_5222,c_5232]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_11476,plain,
% 15.38/2.49      ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7,u1_struct_0(sK6)) = k1_relat_1(sK7) ),
% 15.38/2.49      inference(light_normalisation,[status(thm)],[c_11454,c_10013]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_12463,plain,
% 15.38/2.49      ( k8_relset_1(k2_struct_0(sK5),k1_xboole_0,sK7,k1_xboole_0) = k1_relat_1(sK7) ),
% 15.38/2.49      inference(light_normalisation,[status(thm)],[c_11476,c_10857,c_10861]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_12799,plain,
% 15.38/2.49      ( m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k1_xboole_0))) != iProver_top ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_12463,c_5233]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_12867,plain,
% 15.38/2.49      ( m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top
% 15.38/2.49      | m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.38/2.49      inference(demodulation,[status(thm)],[c_12799,c_9]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_11521,plain,
% 15.38/2.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
% 15.38/2.49      inference(demodulation,[status(thm)],[c_10857,c_5222]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_12130,plain,
% 15.38/2.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k1_xboole_0))) = iProver_top ),
% 15.38/2.49      inference(demodulation,[status(thm)],[c_10861,c_11521]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_12148,plain,
% 15.38/2.49      ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.38/2.49      inference(demodulation,[status(thm)],[c_12130,c_9]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_13757,plain,
% 15.38/2.49      ( m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(k2_struct_0(sK5))) = iProver_top ),
% 15.38/2.49      inference(global_propositional_subsumption,
% 15.38/2.49                [status(thm)],
% 15.38/2.49                [c_12867,c_12148]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_50,plain,
% 15.38/2.49      ( v4_pre_topc(X0,X1)
% 15.38/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.38/2.49      | ~ v1_tdlat_3(X1)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X1) ),
% 15.38/2.49      inference(cnf_transformation,[],[f141]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_30,plain,
% 15.38/2.49      ( ~ v4_pre_topc(X0,X1)
% 15.38/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | k2_pre_topc(X1,X0) = X0 ),
% 15.38/2.49      inference(cnf_transformation,[],[f122]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_872,plain,
% 15.38/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.38/2.49      | ~ v1_tdlat_3(X1)
% 15.38/2.49      | ~ v2_pre_topc(X1)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | k2_pre_topc(X1,X0) = X0 ),
% 15.38/2.49      inference(resolution,[status(thm)],[c_50,c_30]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_44,plain,
% 15.38/2.49      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 15.38/2.49      inference(cnf_transformation,[],[f137]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_886,plain,
% 15.38/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.38/2.49      | ~ v1_tdlat_3(X1)
% 15.38/2.49      | ~ l1_pre_topc(X1)
% 15.38/2.49      | k2_pre_topc(X1,X0) = X0 ),
% 15.38/2.49      inference(forward_subsumption_resolution,[status(thm)],[c_872,c_44]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_5213,plain,
% 15.38/2.49      ( k2_pre_topc(X0,X1) = X1
% 15.38/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.38/2.49      | v1_tdlat_3(X0) != iProver_top
% 15.38/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_886]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_11943,plain,
% 15.38/2.49      ( k2_pre_topc(sK5,X0) = X0
% 15.38/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK5))) != iProver_top
% 15.38/2.49      | v1_tdlat_3(sK5) != iProver_top
% 15.38/2.49      | l1_pre_topc(sK5) != iProver_top ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_10857,c_5213]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_61,plain,
% 15.38/2.49      ( v1_tdlat_3(sK5) = iProver_top ),
% 15.38/2.49      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_13210,plain,
% 15.38/2.49      ( k2_pre_topc(sK5,X0) = X0
% 15.38/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK5))) != iProver_top ),
% 15.38/2.49      inference(global_propositional_subsumption,
% 15.38/2.49                [status(thm)],
% 15.38/2.49                [c_11943,c_61,c_62]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_13763,plain,
% 15.38/2.49      ( k2_pre_topc(sK5,k1_relat_1(sK7)) = k1_relat_1(sK7) ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_13757,c_13210]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_20371,plain,
% 15.38/2.49      ( r1_tarski(k1_relat_1(sK7),k8_relset_1(k2_struct_0(sK5),k1_xboole_0,sK7,k2_pre_topc(sK6,k1_xboole_0))) != iProver_top ),
% 15.38/2.49      inference(light_normalisation,[status(thm)],[c_20364,c_12463,c_13763]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_49688,plain,
% 15.38/2.49      ( r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK5),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK6,k1_xboole_0))) != iProver_top ),
% 15.38/2.49      inference(demodulation,[status(thm)],[c_49597,c_20371]) ).
% 15.38/2.49  
% 15.38/2.49  cnf(c_59756,plain,
% 15.38/2.49      ( $false ),
% 15.38/2.49      inference(superposition,[status(thm)],[c_59725,c_49688]) ).
% 15.38/2.49  
% 15.38/2.49  
% 15.38/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.38/2.49  
% 15.38/2.49  ------                               Statistics
% 15.38/2.49  
% 15.38/2.49  ------ Selected
% 15.38/2.49  
% 15.38/2.49  total_time:                             1.606
% 15.38/2.49  
%------------------------------------------------------------------------------
