%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:46 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  282 (34063 expanded)
%              Number of clauses        :  199 (8771 expanded)
%              Number of leaves         :   23 (10354 expanded)
%              Depth                    :   39
%              Number of atoms          : 1311 (306888 expanded)
%              Number of equality atoms :  611 (39243 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,u1_struct_0(X1))
                     => k1_funct_1(X2,X3) = X3 ) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,u1_struct_0(X1))
                       => k1_funct_1(X2,X3) = X3 ) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
          & ! [X3] :
              ( k1_funct_1(X2,X3) = X3
              | ~ r2_hidden(X3,u1_struct_0(X1))
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK4)
        & ! [X3] :
            ( k1_funct_1(sK4,X3) = X3
            | ~ r2_hidden(X3,u1_struct_0(X1))
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k4_tmap_1(X0,sK3),X2)
            & ! [X3] :
                ( k1_funct_1(X2,X3) = X3
                | ~ r2_hidden(X3,u1_struct_0(sK3))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
                & ! [X3] :
                    ( k1_funct_1(X2,X3) = X3
                    | ~ r2_hidden(X3,u1_struct_0(X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK2),k4_tmap_1(sK2,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4)
    & ! [X3] :
        ( k1_funct_1(sK4,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f50,f49,f48])).

fof(f83,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

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

fof(f38,plain,(
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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X2] :
                    ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                    | ~ r2_hidden(X2,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X2] :
                    ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                    | ~ r2_hidden(X2,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
        & m1_subset_1(sK0(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
                & m1_subset_1(sK0(X0,X2,X3),X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | m1_subset_1(sK0(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
      | ~ m1_subset_1(X5,X0)
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,u1_struct_0(X1))
               => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f87,plain,(
    ! [X3] :
      ( k1_funct_1(sK4,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_502,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_35])).

cnf(c_503,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_507,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_503,c_36,c_34])).

cnf(c_591,plain,
    ( m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_507])).

cnf(c_592,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_1729,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1739,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3564,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_1739])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1745,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2484,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(k4_tmap_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_1729,c_1745])).

cnf(c_3568,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3564,c_2484])).

cnf(c_20,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_403,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_421,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_403])).

cnf(c_535,plain,
    ( v2_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_421,c_34])).

cnf(c_536,plain,
    ( v2_struct_0(sK2)
    | u1_struct_0(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_24,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_439,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_440,plain,
    ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_444,plain,
    ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_36,c_34])).

cnf(c_626,plain,
    ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_444])).

cnf(c_627,plain,
    ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_628,plain,
    ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_5093,plain,
    ( k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3568,c_36,c_536,c_628])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1733,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3563,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),sK4) = u1_struct_0(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1733,c_1739])).

cnf(c_2367,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1733,c_1745])).

cnf(c_3575,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK4)
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3563,c_2367])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_43,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3793,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3575,c_36,c_43,c_536])).

cnf(c_5095,plain,
    ( k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_5093,c_3793])).

cnf(c_17,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1737,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5101,plain,
    ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5095,c_1737])).

cnf(c_5260,plain,
    ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5101,c_5095])).

cnf(c_593,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_484,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_35])).

cnf(c_485,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_funct_1(k4_tmap_1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_489,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v1_funct_1(k4_tmap_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_485,c_36,c_34])).

cnf(c_598,plain,
    ( v1_funct_1(k4_tmap_1(sK2,X0))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_489])).

cnf(c_599,plain,
    ( v1_funct_1(k4_tmap_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_600,plain,
    ( v1_funct_1(k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2004,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v1_relat_1(k4_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2005,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2004])).

cnf(c_6224,plain,
    ( v1_relat_1(X0) != iProver_top
    | r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5260,c_593,c_600,c_2005])).

cnf(c_6225,plain,
    ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6224])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1747,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6235,plain,
    ( m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6225,c_1747])).

cnf(c_14,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK0(X0,X2,X3),X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_15,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X3,X4) = k1_funct_1(X2,X4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_801,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK0(X1,X0,X3),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,X4) = k1_funct_1(X3,X4) ),
    inference(resolution,[status(thm)],[c_14,c_15])).

cnf(c_1725,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | v1_funct_2(X0,X3,X4) != iProver_top
    | v1_funct_2(X2,X3,X4) != iProver_top
    | m1_subset_1(X1,X3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) != iProver_top
    | m1_subset_1(sK0(X3,X0,X2),X3) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_3411,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
    | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),X1,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_1725])).

cnf(c_4903,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),X1,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
    | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3411,c_600,c_628])).

cnf(c_4904,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
    | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),X1,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4903])).

cnf(c_4909,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
    | v1_funct_2(X1,k1_relat_1(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_relat_1(sK4)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X1,k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4904,c_3793])).

cnf(c_6311,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(X1,sK1(k4_tmap_1(sK2,sK3),X0))
    | v1_funct_2(X1,k1_relat_1(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X1,k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6235,c_4909])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_543,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_544,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_548,plain,
    ( v2_struct_0(X0)
    | m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_544,c_36])).

cnf(c_549,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_548])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(X1)
    | sK2 != sK2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_549])).

cnf(c_574,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_574,c_33])).

cnf(c_579,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_578])).

cnf(c_1730,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_3800,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3793,c_1730])).

cnf(c_9895,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(X1,sK1(k4_tmap_1(sK2,sK3),X0))
    | v1_funct_2(X1,k1_relat_1(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X1,k4_tmap_1(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6311,c_3800])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_457,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_458,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ r2_hidden(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k1_funct_1(k4_tmap_1(sK2,X0),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_462,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ r2_hidden(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(X0)
    | k1_funct_1(k4_tmap_1(sK2,X0),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_36,c_34])).

cnf(c_605,plain,
    ( ~ r2_hidden(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(X1)
    | k1_funct_1(k4_tmap_1(sK2,X1),X0) = X0
    | sK2 != sK2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_462])).

cnf(c_606,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_610,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_606,c_33])).

cnf(c_611,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
    inference(renaming,[status(thm)],[c_610])).

cnf(c_1727,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_3799,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3793,c_1727])).

cnf(c_4689,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_3799])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2001,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2002,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2001])).

cnf(c_3634,plain,
    ( m1_subset_1(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_1747])).

cnf(c_4666,plain,
    ( m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3634,c_3800])).

cnf(c_5960,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4689,c_42,c_44,c_2002,c_4666])).

cnf(c_5961,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5960])).

cnf(c_5973,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5095,c_5961])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2036,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(sK4))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2110,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ r1_tarski(sK4,sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2036])).

cnf(c_2111,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(sK4,sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2110])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2228,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2229,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2228])).

cnf(c_7980,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5973,c_42,c_44,c_593,c_600,c_2002,c_2005,c_2111,c_2229])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1749,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7988,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7980,c_1749])).

cnf(c_13,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_876,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k4_tmap_1(sK2,sK3) != X0
    | k1_funct_1(X3,sK0(X1,X0,X3)) != k1_funct_1(X0,sK0(X1,X0,X3))
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK3) != X1
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_877,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_876])).

cnf(c_1245,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2028,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != X0
    | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != X0
    | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_2288,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != k1_funct_1(X0,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4))
    | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != k1_funct_1(X0,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4))
    | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_2028])).

cnf(c_2850,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4))
    | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4))
    | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_2288])).

cnf(c_1244,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2851,plain,
    ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1244])).

cnf(c_1254,plain,
    ( X0 != X1
    | X2 != X3
    | k1_funct_1(X0,X2) = k1_funct_1(X1,X3) ),
    theory(equality)).

cnf(c_4054,plain,
    ( sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) != sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)
    | k4_tmap_1(sK2,sK3) != sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_4423,plain,
    ( sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) = sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1244])).

cnf(c_8143,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7988,c_31,c_30,c_29,c_592,c_599,c_627,c_877,c_2850,c_2851,c_4054,c_4423])).

cnf(c_11029,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(X0,sK1(k4_tmap_1(sK2,sK3),sK4))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | v1_funct_2(X0,k1_relat_1(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,k4_tmap_1(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9895,c_8143])).

cnf(c_1748,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6237,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6225,c_3799])).

cnf(c_6312,plain,
    ( m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6235,c_3800])).

cnf(c_6751,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6237,c_6312])).

cnf(c_6762,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_6751])).

cnf(c_7229,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6762,c_42,c_44,c_2002])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_tarski(X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1736,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5098,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5095,c_1736])).

cnf(c_5743,plain,
    ( v1_relat_1(X1) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5098,c_593,c_600,c_2005])).

cnf(c_5744,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5743])).

cnf(c_7240,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7229,c_5744])).

cnf(c_11963,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7240,c_42,c_44,c_2002])).

cnf(c_11972,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_11963])).

cnf(c_12092,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11972,c_42,c_44,c_2002])).

cnf(c_12093,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12092])).

cnf(c_12107,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5095,c_12093])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2508,plain,
    ( r1_tarski(X0,k4_tmap_1(sK2,sK3))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(k4_tmap_1(sK2,sK3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k4_tmap_1(sK2,sK3))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(X0,k4_tmap_1(sK2,sK3))) != k1_funct_1(X0,sK1(X0,k4_tmap_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3606,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3))
    | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(k4_tmap_1(sK2,sK3))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) != k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_2508])).

cnf(c_3607,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) != k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3606])).

cnf(c_4470,plain,
    ( k1_relat_1(sK4) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1244])).

cnf(c_1246,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3695,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
    | k1_relat_1(k4_tmap_1(sK2,sK3)) != X1
    | k1_relat_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_4469,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),X0)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
    | k1_relat_1(k4_tmap_1(sK2,sK3)) != X0
    | k1_relat_1(sK4) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3695])).

cnf(c_6994,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | k1_relat_1(k4_tmap_1(sK2,sK3)) != k1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4469])).

cnf(c_6995,plain,
    ( k1_relat_1(k4_tmap_1(sK2,sK3)) != k1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6994])).

cnf(c_7237,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7229,c_1749])).

cnf(c_7276,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7237,c_31,c_30,c_29,c_592,c_599,c_627,c_877,c_2850,c_2851,c_4054,c_4423])).

cnf(c_12998,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12107,c_42,c_44,c_593,c_600,c_2002,c_2005,c_2111,c_2229,c_3607,c_4470,c_5095,c_6995,c_7276])).

cnf(c_1738,plain,
    ( k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | r1_tarski(X1,X0) = iProver_top
    | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13018,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_12998,c_1738])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k1_funct_1(sK4,X0) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1734,plain,
    ( k1_funct_1(sK4,X0) = X0
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3806,plain,
    ( k1_funct_1(sK4,X0) = X0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3793,c_1734])).

cnf(c_6238,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6225,c_3806])).

cnf(c_6412,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6238,c_6312])).

cnf(c_6423,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_6412])).

cnf(c_6458,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6423,c_42,c_44,c_2002])).

cnf(c_6469,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6458,c_5744])).

cnf(c_7686,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6469,c_42,c_44,c_2002])).

cnf(c_7695,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_7686])).

cnf(c_9200,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7695,c_42,c_44,c_2002])).

cnf(c_9201,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9200])).

cnf(c_9215,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5095,c_9201])).

cnf(c_6466,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6458,c_1749])).

cnf(c_7122,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6466,c_31,c_30,c_29,c_592,c_599,c_627,c_877,c_2850,c_2851,c_4054,c_4423])).

cnf(c_7124,plain,
    ( ~ r1_tarski(sK4,k4_tmap_1(sK2,sK3))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7122])).

cnf(c_9233,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3))
    | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
    | ~ v1_relat_1(k4_tmap_1(sK2,sK3))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9215])).

cnf(c_9696,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9215,c_31,c_42,c_29,c_44,c_592,c_593,c_599,c_600,c_2001,c_2002,c_2004,c_2005,c_2110,c_2111,c_2228,c_2229,c_3607,c_4470,c_5095,c_6995,c_7122,c_7124,c_9233])).

cnf(c_13019,plain,
    ( sK1(k4_tmap_1(sK2,sK3),sK4) != sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13018,c_5095,c_9696])).

cnf(c_13020,plain,
    ( r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13019])).

cnf(c_13023,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11029,c_31,c_42,c_30,c_29,c_44,c_592,c_593,c_599,c_600,c_627,c_877,c_2002,c_2005,c_2111,c_2229,c_2850,c_2851,c_4054,c_4423,c_7988,c_13020])).

cnf(c_13074,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) != sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_13023,c_1738])).

cnf(c_13075,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) != sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13074,c_5095])).

cnf(c_2094,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_11925,plain,
    ( ~ r1_tarski(k4_tmap_1(sK2,sK3),sK4)
    | ~ r1_tarski(sK4,k4_tmap_1(sK2,sK3))
    | k4_tmap_1(sK2,sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_2094])).

cnf(c_11926,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11925])).

cnf(c_5893,plain,
    ( v1_relat_1(X0) != iProver_top
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4666,c_42,c_44,c_2002])).

cnf(c_5894,plain,
    ( m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5893])).

cnf(c_3979,plain,
    ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_3806])).

cnf(c_4188,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3979,c_42,c_44,c_2002])).

cnf(c_4189,plain,
    ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4188])).

cnf(c_5904,plain,
    ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5894,c_4189])).

cnf(c_5916,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5095,c_5904])).

cnf(c_7770,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5916,c_42,c_44,c_593,c_600,c_2002,c_2005,c_2111,c_2229])).

cnf(c_7778,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7770,c_1749])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13075,c_13020,c_11926,c_7778,c_4423,c_4054,c_2851,c_2850,c_2229,c_2111,c_2005,c_2002,c_877,c_627,c_600,c_599,c_593,c_592,c_44,c_29,c_30,c_42,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:51:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.86/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.86/0.99  
% 3.86/0.99  ------  iProver source info
% 3.86/0.99  
% 3.86/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.86/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.86/0.99  git: non_committed_changes: false
% 3.86/0.99  git: last_make_outside_of_git: false
% 3.86/0.99  
% 3.86/0.99  ------ 
% 3.86/0.99  
% 3.86/0.99  ------ Input Options
% 3.86/0.99  
% 3.86/0.99  --out_options                           all
% 3.86/0.99  --tptp_safe_out                         true
% 3.86/0.99  --problem_path                          ""
% 3.86/0.99  --include_path                          ""
% 3.86/0.99  --clausifier                            res/vclausify_rel
% 3.86/0.99  --clausifier_options                    --mode clausify
% 3.86/0.99  --stdin                                 false
% 3.86/0.99  --stats_out                             all
% 3.86/0.99  
% 3.86/0.99  ------ General Options
% 3.86/0.99  
% 3.86/0.99  --fof                                   false
% 3.86/0.99  --time_out_real                         305.
% 3.86/0.99  --time_out_virtual                      -1.
% 3.86/0.99  --symbol_type_check                     false
% 3.86/0.99  --clausify_out                          false
% 3.86/0.99  --sig_cnt_out                           false
% 3.86/0.99  --trig_cnt_out                          false
% 3.86/0.99  --trig_cnt_out_tolerance                1.
% 3.86/0.99  --trig_cnt_out_sk_spl                   false
% 3.86/0.99  --abstr_cl_out                          false
% 3.86/0.99  
% 3.86/0.99  ------ Global Options
% 3.86/0.99  
% 3.86/0.99  --schedule                              default
% 3.86/0.99  --add_important_lit                     false
% 3.86/0.99  --prop_solver_per_cl                    1000
% 3.86/0.99  --min_unsat_core                        false
% 3.86/0.99  --soft_assumptions                      false
% 3.86/0.99  --soft_lemma_size                       3
% 3.86/0.99  --prop_impl_unit_size                   0
% 3.86/0.99  --prop_impl_unit                        []
% 3.86/0.99  --share_sel_clauses                     true
% 3.86/0.99  --reset_solvers                         false
% 3.86/0.99  --bc_imp_inh                            [conj_cone]
% 3.86/0.99  --conj_cone_tolerance                   3.
% 3.86/0.99  --extra_neg_conj                        none
% 3.86/0.99  --large_theory_mode                     true
% 3.86/0.99  --prolific_symb_bound                   200
% 3.86/0.99  --lt_threshold                          2000
% 3.86/0.99  --clause_weak_htbl                      true
% 3.86/0.99  --gc_record_bc_elim                     false
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing Options
% 3.86/0.99  
% 3.86/0.99  --preprocessing_flag                    true
% 3.86/0.99  --time_out_prep_mult                    0.1
% 3.86/0.99  --splitting_mode                        input
% 3.86/0.99  --splitting_grd                         true
% 3.86/0.99  --splitting_cvd                         false
% 3.86/0.99  --splitting_cvd_svl                     false
% 3.86/0.99  --splitting_nvd                         32
% 3.86/0.99  --sub_typing                            true
% 3.86/0.99  --prep_gs_sim                           true
% 3.86/0.99  --prep_unflatten                        true
% 3.86/0.99  --prep_res_sim                          true
% 3.86/0.99  --prep_upred                            true
% 3.86/0.99  --prep_sem_filter                       exhaustive
% 3.86/0.99  --prep_sem_filter_out                   false
% 3.86/0.99  --pred_elim                             true
% 3.86/0.99  --res_sim_input                         true
% 3.86/0.99  --eq_ax_congr_red                       true
% 3.86/0.99  --pure_diseq_elim                       true
% 3.86/0.99  --brand_transform                       false
% 3.86/0.99  --non_eq_to_eq                          false
% 3.86/0.99  --prep_def_merge                        true
% 3.86/0.99  --prep_def_merge_prop_impl              false
% 3.86/0.99  --prep_def_merge_mbd                    true
% 3.86/0.99  --prep_def_merge_tr_red                 false
% 3.86/0.99  --prep_def_merge_tr_cl                  false
% 3.86/0.99  --smt_preprocessing                     true
% 3.86/0.99  --smt_ac_axioms                         fast
% 3.86/0.99  --preprocessed_out                      false
% 3.86/0.99  --preprocessed_stats                    false
% 3.86/0.99  
% 3.86/0.99  ------ Abstraction refinement Options
% 3.86/0.99  
% 3.86/0.99  --abstr_ref                             []
% 3.86/0.99  --abstr_ref_prep                        false
% 3.86/0.99  --abstr_ref_until_sat                   false
% 3.86/0.99  --abstr_ref_sig_restrict                funpre
% 3.86/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.86/0.99  --abstr_ref_under                       []
% 3.86/0.99  
% 3.86/0.99  ------ SAT Options
% 3.86/0.99  
% 3.86/0.99  --sat_mode                              false
% 3.86/0.99  --sat_fm_restart_options                ""
% 3.86/0.99  --sat_gr_def                            false
% 3.86/0.99  --sat_epr_types                         true
% 3.86/0.99  --sat_non_cyclic_types                  false
% 3.86/0.99  --sat_finite_models                     false
% 3.86/0.99  --sat_fm_lemmas                         false
% 3.86/0.99  --sat_fm_prep                           false
% 3.86/0.99  --sat_fm_uc_incr                        true
% 3.86/0.99  --sat_out_model                         small
% 3.86/0.99  --sat_out_clauses                       false
% 3.86/0.99  
% 3.86/0.99  ------ QBF Options
% 3.86/0.99  
% 3.86/0.99  --qbf_mode                              false
% 3.86/0.99  --qbf_elim_univ                         false
% 3.86/0.99  --qbf_dom_inst                          none
% 3.86/0.99  --qbf_dom_pre_inst                      false
% 3.86/0.99  --qbf_sk_in                             false
% 3.86/0.99  --qbf_pred_elim                         true
% 3.86/0.99  --qbf_split                             512
% 3.86/0.99  
% 3.86/0.99  ------ BMC1 Options
% 3.86/0.99  
% 3.86/0.99  --bmc1_incremental                      false
% 3.86/0.99  --bmc1_axioms                           reachable_all
% 3.86/0.99  --bmc1_min_bound                        0
% 3.86/0.99  --bmc1_max_bound                        -1
% 3.86/0.99  --bmc1_max_bound_default                -1
% 3.86/0.99  --bmc1_symbol_reachability              true
% 3.86/0.99  --bmc1_property_lemmas                  false
% 3.86/0.99  --bmc1_k_induction                      false
% 3.86/0.99  --bmc1_non_equiv_states                 false
% 3.86/0.99  --bmc1_deadlock                         false
% 3.86/0.99  --bmc1_ucm                              false
% 3.86/0.99  --bmc1_add_unsat_core                   none
% 3.86/0.99  --bmc1_unsat_core_children              false
% 3.86/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.86/0.99  --bmc1_out_stat                         full
% 3.86/0.99  --bmc1_ground_init                      false
% 3.86/0.99  --bmc1_pre_inst_next_state              false
% 3.86/0.99  --bmc1_pre_inst_state                   false
% 3.86/0.99  --bmc1_pre_inst_reach_state             false
% 3.86/0.99  --bmc1_out_unsat_core                   false
% 3.86/0.99  --bmc1_aig_witness_out                  false
% 3.86/0.99  --bmc1_verbose                          false
% 3.86/0.99  --bmc1_dump_clauses_tptp                false
% 3.86/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.86/0.99  --bmc1_dump_file                        -
% 3.86/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.86/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.86/0.99  --bmc1_ucm_extend_mode                  1
% 3.86/0.99  --bmc1_ucm_init_mode                    2
% 3.86/0.99  --bmc1_ucm_cone_mode                    none
% 3.86/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.86/0.99  --bmc1_ucm_relax_model                  4
% 3.86/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.86/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.86/0.99  --bmc1_ucm_layered_model                none
% 3.86/0.99  --bmc1_ucm_max_lemma_size               10
% 3.86/0.99  
% 3.86/0.99  ------ AIG Options
% 3.86/0.99  
% 3.86/0.99  --aig_mode                              false
% 3.86/0.99  
% 3.86/0.99  ------ Instantiation Options
% 3.86/0.99  
% 3.86/0.99  --instantiation_flag                    true
% 3.86/0.99  --inst_sos_flag                         false
% 3.86/0.99  --inst_sos_phase                        true
% 3.86/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel_side                     num_symb
% 3.86/0.99  --inst_solver_per_active                1400
% 3.86/0.99  --inst_solver_calls_frac                1.
% 3.86/0.99  --inst_passive_queue_type               priority_queues
% 3.86/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.86/0.99  --inst_passive_queues_freq              [25;2]
% 3.86/0.99  --inst_dismatching                      true
% 3.86/0.99  --inst_eager_unprocessed_to_passive     true
% 3.86/0.99  --inst_prop_sim_given                   true
% 3.86/0.99  --inst_prop_sim_new                     false
% 3.86/0.99  --inst_subs_new                         false
% 3.86/0.99  --inst_eq_res_simp                      false
% 3.86/0.99  --inst_subs_given                       false
% 3.86/0.99  --inst_orphan_elimination               true
% 3.86/0.99  --inst_learning_loop_flag               true
% 3.86/0.99  --inst_learning_start                   3000
% 3.86/0.99  --inst_learning_factor                  2
% 3.86/0.99  --inst_start_prop_sim_after_learn       3
% 3.86/0.99  --inst_sel_renew                        solver
% 3.86/0.99  --inst_lit_activity_flag                true
% 3.86/0.99  --inst_restr_to_given                   false
% 3.86/0.99  --inst_activity_threshold               500
% 3.86/0.99  --inst_out_proof                        true
% 3.86/0.99  
% 3.86/0.99  ------ Resolution Options
% 3.86/0.99  
% 3.86/0.99  --resolution_flag                       true
% 3.86/0.99  --res_lit_sel                           adaptive
% 3.86/0.99  --res_lit_sel_side                      none
% 3.86/0.99  --res_ordering                          kbo
% 3.86/0.99  --res_to_prop_solver                    active
% 3.86/0.99  --res_prop_simpl_new                    false
% 3.86/0.99  --res_prop_simpl_given                  true
% 3.86/0.99  --res_passive_queue_type                priority_queues
% 3.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.86/0.99  --res_passive_queues_freq               [15;5]
% 3.86/0.99  --res_forward_subs                      full
% 3.86/0.99  --res_backward_subs                     full
% 3.86/0.99  --res_forward_subs_resolution           true
% 3.86/0.99  --res_backward_subs_resolution          true
% 3.86/0.99  --res_orphan_elimination                true
% 3.86/0.99  --res_time_limit                        2.
% 3.86/0.99  --res_out_proof                         true
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Options
% 3.86/0.99  
% 3.86/0.99  --superposition_flag                    true
% 3.86/0.99  --sup_passive_queue_type                priority_queues
% 3.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.86/0.99  --demod_completeness_check              fast
% 3.86/0.99  --demod_use_ground                      true
% 3.86/0.99  --sup_to_prop_solver                    passive
% 3.86/0.99  --sup_prop_simpl_new                    true
% 3.86/0.99  --sup_prop_simpl_given                  true
% 3.86/0.99  --sup_fun_splitting                     false
% 3.86/0.99  --sup_smt_interval                      50000
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Simplification Setup
% 3.86/0.99  
% 3.86/0.99  --sup_indices_passive                   []
% 3.86/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_full_bw                           [BwDemod]
% 3.86/0.99  --sup_immed_triv                        [TrivRules]
% 3.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_immed_bw_main                     []
% 3.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.86/0.99  
% 3.86/0.99  ------ Combination Options
% 3.86/0.99  
% 3.86/0.99  --comb_res_mult                         3
% 3.86/0.99  --comb_sup_mult                         2
% 3.86/0.99  --comb_inst_mult                        10
% 3.86/0.99  
% 3.86/0.99  ------ Debug Options
% 3.86/0.99  
% 3.86/0.99  --dbg_backtrace                         false
% 3.86/0.99  --dbg_dump_prop_clauses                 false
% 3.86/0.99  --dbg_dump_prop_clauses_file            -
% 3.86/0.99  --dbg_out_stat                          false
% 3.86/0.99  ------ Parsing...
% 3.86/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.86/0.99  ------ Proving...
% 3.86/0.99  ------ Problem Properties 
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  clauses                                 29
% 3.86/0.99  conjectures                             4
% 3.86/0.99  EPR                                     4
% 3.86/0.99  Horn                                    23
% 3.86/0.99  unary                                   10
% 3.86/0.99  binary                                  4
% 3.86/0.99  lits                                    93
% 3.86/0.99  lits eq                                 20
% 3.86/0.99  fd_pure                                 0
% 3.86/0.99  fd_pseudo                               0
% 3.86/0.99  fd_cond                                 3
% 3.86/0.99  fd_pseudo_cond                          1
% 3.86/0.99  AC symbols                              0
% 3.86/0.99  
% 3.86/0.99  ------ Schedule dynamic 5 is on 
% 3.86/0.99  
% 3.86/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  ------ 
% 3.86/0.99  Current options:
% 3.86/0.99  ------ 
% 3.86/0.99  
% 3.86/0.99  ------ Input Options
% 3.86/0.99  
% 3.86/0.99  --out_options                           all
% 3.86/0.99  --tptp_safe_out                         true
% 3.86/0.99  --problem_path                          ""
% 3.86/0.99  --include_path                          ""
% 3.86/0.99  --clausifier                            res/vclausify_rel
% 3.86/0.99  --clausifier_options                    --mode clausify
% 3.86/0.99  --stdin                                 false
% 3.86/0.99  --stats_out                             all
% 3.86/0.99  
% 3.86/0.99  ------ General Options
% 3.86/0.99  
% 3.86/0.99  --fof                                   false
% 3.86/0.99  --time_out_real                         305.
% 3.86/0.99  --time_out_virtual                      -1.
% 3.86/0.99  --symbol_type_check                     false
% 3.86/0.99  --clausify_out                          false
% 3.86/0.99  --sig_cnt_out                           false
% 3.86/0.99  --trig_cnt_out                          false
% 3.86/0.99  --trig_cnt_out_tolerance                1.
% 3.86/0.99  --trig_cnt_out_sk_spl                   false
% 3.86/0.99  --abstr_cl_out                          false
% 3.86/0.99  
% 3.86/0.99  ------ Global Options
% 3.86/0.99  
% 3.86/0.99  --schedule                              default
% 3.86/0.99  --add_important_lit                     false
% 3.86/0.99  --prop_solver_per_cl                    1000
% 3.86/0.99  --min_unsat_core                        false
% 3.86/0.99  --soft_assumptions                      false
% 3.86/0.99  --soft_lemma_size                       3
% 3.86/0.99  --prop_impl_unit_size                   0
% 3.86/0.99  --prop_impl_unit                        []
% 3.86/0.99  --share_sel_clauses                     true
% 3.86/0.99  --reset_solvers                         false
% 3.86/0.99  --bc_imp_inh                            [conj_cone]
% 3.86/0.99  --conj_cone_tolerance                   3.
% 3.86/0.99  --extra_neg_conj                        none
% 3.86/0.99  --large_theory_mode                     true
% 3.86/0.99  --prolific_symb_bound                   200
% 3.86/0.99  --lt_threshold                          2000
% 3.86/0.99  --clause_weak_htbl                      true
% 3.86/0.99  --gc_record_bc_elim                     false
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing Options
% 3.86/0.99  
% 3.86/0.99  --preprocessing_flag                    true
% 3.86/0.99  --time_out_prep_mult                    0.1
% 3.86/0.99  --splitting_mode                        input
% 3.86/0.99  --splitting_grd                         true
% 3.86/0.99  --splitting_cvd                         false
% 3.86/0.99  --splitting_cvd_svl                     false
% 3.86/0.99  --splitting_nvd                         32
% 3.86/0.99  --sub_typing                            true
% 3.86/0.99  --prep_gs_sim                           true
% 3.86/0.99  --prep_unflatten                        true
% 3.86/0.99  --prep_res_sim                          true
% 3.86/0.99  --prep_upred                            true
% 3.86/0.99  --prep_sem_filter                       exhaustive
% 3.86/0.99  --prep_sem_filter_out                   false
% 3.86/0.99  --pred_elim                             true
% 3.86/0.99  --res_sim_input                         true
% 3.86/0.99  --eq_ax_congr_red                       true
% 3.86/0.99  --pure_diseq_elim                       true
% 3.86/0.99  --brand_transform                       false
% 3.86/0.99  --non_eq_to_eq                          false
% 3.86/0.99  --prep_def_merge                        true
% 3.86/0.99  --prep_def_merge_prop_impl              false
% 3.86/0.99  --prep_def_merge_mbd                    true
% 3.86/0.99  --prep_def_merge_tr_red                 false
% 3.86/0.99  --prep_def_merge_tr_cl                  false
% 3.86/0.99  --smt_preprocessing                     true
% 3.86/0.99  --smt_ac_axioms                         fast
% 3.86/0.99  --preprocessed_out                      false
% 3.86/0.99  --preprocessed_stats                    false
% 3.86/0.99  
% 3.86/0.99  ------ Abstraction refinement Options
% 3.86/0.99  
% 3.86/0.99  --abstr_ref                             []
% 3.86/0.99  --abstr_ref_prep                        false
% 3.86/0.99  --abstr_ref_until_sat                   false
% 3.86/0.99  --abstr_ref_sig_restrict                funpre
% 3.86/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.86/0.99  --abstr_ref_under                       []
% 3.86/0.99  
% 3.86/0.99  ------ SAT Options
% 3.86/0.99  
% 3.86/0.99  --sat_mode                              false
% 3.86/0.99  --sat_fm_restart_options                ""
% 3.86/0.99  --sat_gr_def                            false
% 3.86/0.99  --sat_epr_types                         true
% 3.86/0.99  --sat_non_cyclic_types                  false
% 3.86/0.99  --sat_finite_models                     false
% 3.86/0.99  --sat_fm_lemmas                         false
% 3.86/0.99  --sat_fm_prep                           false
% 3.86/0.99  --sat_fm_uc_incr                        true
% 3.86/0.99  --sat_out_model                         small
% 3.86/0.99  --sat_out_clauses                       false
% 3.86/0.99  
% 3.86/0.99  ------ QBF Options
% 3.86/0.99  
% 3.86/0.99  --qbf_mode                              false
% 3.86/0.99  --qbf_elim_univ                         false
% 3.86/0.99  --qbf_dom_inst                          none
% 3.86/0.99  --qbf_dom_pre_inst                      false
% 3.86/0.99  --qbf_sk_in                             false
% 3.86/0.99  --qbf_pred_elim                         true
% 3.86/0.99  --qbf_split                             512
% 3.86/0.99  
% 3.86/0.99  ------ BMC1 Options
% 3.86/0.99  
% 3.86/0.99  --bmc1_incremental                      false
% 3.86/0.99  --bmc1_axioms                           reachable_all
% 3.86/0.99  --bmc1_min_bound                        0
% 3.86/0.99  --bmc1_max_bound                        -1
% 3.86/0.99  --bmc1_max_bound_default                -1
% 3.86/0.99  --bmc1_symbol_reachability              true
% 3.86/0.99  --bmc1_property_lemmas                  false
% 3.86/0.99  --bmc1_k_induction                      false
% 3.86/0.99  --bmc1_non_equiv_states                 false
% 3.86/0.99  --bmc1_deadlock                         false
% 3.86/0.99  --bmc1_ucm                              false
% 3.86/0.99  --bmc1_add_unsat_core                   none
% 3.86/0.99  --bmc1_unsat_core_children              false
% 3.86/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.86/0.99  --bmc1_out_stat                         full
% 3.86/0.99  --bmc1_ground_init                      false
% 3.86/0.99  --bmc1_pre_inst_next_state              false
% 3.86/0.99  --bmc1_pre_inst_state                   false
% 3.86/0.99  --bmc1_pre_inst_reach_state             false
% 3.86/0.99  --bmc1_out_unsat_core                   false
% 3.86/0.99  --bmc1_aig_witness_out                  false
% 3.86/0.99  --bmc1_verbose                          false
% 3.86/0.99  --bmc1_dump_clauses_tptp                false
% 3.86/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.86/0.99  --bmc1_dump_file                        -
% 3.86/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.86/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.86/0.99  --bmc1_ucm_extend_mode                  1
% 3.86/0.99  --bmc1_ucm_init_mode                    2
% 3.86/0.99  --bmc1_ucm_cone_mode                    none
% 3.86/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.86/0.99  --bmc1_ucm_relax_model                  4
% 3.86/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.86/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.86/0.99  --bmc1_ucm_layered_model                none
% 3.86/0.99  --bmc1_ucm_max_lemma_size               10
% 3.86/0.99  
% 3.86/0.99  ------ AIG Options
% 3.86/0.99  
% 3.86/0.99  --aig_mode                              false
% 3.86/0.99  
% 3.86/0.99  ------ Instantiation Options
% 3.86/0.99  
% 3.86/0.99  --instantiation_flag                    true
% 3.86/0.99  --inst_sos_flag                         false
% 3.86/0.99  --inst_sos_phase                        true
% 3.86/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel_side                     none
% 3.86/0.99  --inst_solver_per_active                1400
% 3.86/0.99  --inst_solver_calls_frac                1.
% 3.86/0.99  --inst_passive_queue_type               priority_queues
% 3.86/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.86/0.99  --inst_passive_queues_freq              [25;2]
% 3.86/0.99  --inst_dismatching                      true
% 3.86/0.99  --inst_eager_unprocessed_to_passive     true
% 3.86/0.99  --inst_prop_sim_given                   true
% 3.86/0.99  --inst_prop_sim_new                     false
% 3.86/0.99  --inst_subs_new                         false
% 3.86/0.99  --inst_eq_res_simp                      false
% 3.86/0.99  --inst_subs_given                       false
% 3.86/0.99  --inst_orphan_elimination               true
% 3.86/0.99  --inst_learning_loop_flag               true
% 3.86/0.99  --inst_learning_start                   3000
% 3.86/0.99  --inst_learning_factor                  2
% 3.86/0.99  --inst_start_prop_sim_after_learn       3
% 3.86/0.99  --inst_sel_renew                        solver
% 3.86/0.99  --inst_lit_activity_flag                true
% 3.86/0.99  --inst_restr_to_given                   false
% 3.86/0.99  --inst_activity_threshold               500
% 3.86/0.99  --inst_out_proof                        true
% 3.86/0.99  
% 3.86/0.99  ------ Resolution Options
% 3.86/0.99  
% 3.86/0.99  --resolution_flag                       false
% 3.86/0.99  --res_lit_sel                           adaptive
% 3.86/0.99  --res_lit_sel_side                      none
% 3.86/0.99  --res_ordering                          kbo
% 3.86/0.99  --res_to_prop_solver                    active
% 3.86/0.99  --res_prop_simpl_new                    false
% 3.86/0.99  --res_prop_simpl_given                  true
% 3.86/0.99  --res_passive_queue_type                priority_queues
% 3.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.86/0.99  --res_passive_queues_freq               [15;5]
% 3.86/0.99  --res_forward_subs                      full
% 3.86/0.99  --res_backward_subs                     full
% 3.86/0.99  --res_forward_subs_resolution           true
% 3.86/0.99  --res_backward_subs_resolution          true
% 3.86/0.99  --res_orphan_elimination                true
% 3.86/0.99  --res_time_limit                        2.
% 3.86/0.99  --res_out_proof                         true
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Options
% 3.86/0.99  
% 3.86/0.99  --superposition_flag                    true
% 3.86/0.99  --sup_passive_queue_type                priority_queues
% 3.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.86/0.99  --demod_completeness_check              fast
% 3.86/0.99  --demod_use_ground                      true
% 3.86/0.99  --sup_to_prop_solver                    passive
% 3.86/0.99  --sup_prop_simpl_new                    true
% 3.86/0.99  --sup_prop_simpl_given                  true
% 3.86/0.99  --sup_fun_splitting                     false
% 3.86/0.99  --sup_smt_interval                      50000
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Simplification Setup
% 3.86/0.99  
% 3.86/0.99  --sup_indices_passive                   []
% 3.86/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_full_bw                           [BwDemod]
% 3.86/0.99  --sup_immed_triv                        [TrivRules]
% 3.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_immed_bw_main                     []
% 3.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.86/0.99  
% 3.86/0.99  ------ Combination Options
% 3.86/0.99  
% 3.86/0.99  --comb_res_mult                         3
% 3.86/0.99  --comb_sup_mult                         2
% 3.86/0.99  --comb_inst_mult                        10
% 3.86/0.99  
% 3.86/0.99  ------ Debug Options
% 3.86/0.99  
% 3.86/0.99  --dbg_backtrace                         false
% 3.86/0.99  --dbg_dump_prop_clauses                 false
% 3.86/0.99  --dbg_dump_prop_clauses_file            -
% 3.86/0.99  --dbg_out_stat                          false
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  ------ Proving...
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  % SZS status Theorem for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  fof(f14,conjecture,(
% 3.86/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f15,negated_conjecture,(
% 3.86/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 3.86/0.99    inference(negated_conjecture,[],[f14])).
% 3.86/0.99  
% 3.86/0.99  fof(f34,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f15])).
% 3.86/0.99  
% 3.86/0.99  fof(f35,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.86/0.99    inference(flattening,[],[f34])).
% 3.86/0.99  
% 3.86/0.99  fof(f50,plain,(
% 3.86/0.99    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK4) & ! [X3] : (k1_funct_1(sK4,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f49,plain,(
% 3.86/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k4_tmap_1(X0,sK3),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f48,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK2),k4_tmap_1(sK2,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f51,plain,(
% 3.86/0.99    ((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) & ! [X3] : (k1_funct_1(sK4,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f50,f49,f48])).
% 3.86/0.99  
% 3.86/0.99  fof(f83,plain,(
% 3.86/0.99    m1_pre_topc(sK3,sK2)),
% 3.86/0.99    inference(cnf_transformation,[],[f51])).
% 3.86/0.99  
% 3.86/0.99  fof(f12,axiom,(
% 3.86/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f30,plain,(
% 3.86/0.99    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f12])).
% 3.86/0.99  
% 3.86/0.99  fof(f31,plain,(
% 3.86/0.99    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.86/0.99    inference(flattening,[],[f30])).
% 3.86/0.99  
% 3.86/0.99  fof(f77,plain,(
% 3.86/0.99    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f31])).
% 3.86/0.99  
% 3.86/0.99  fof(f80,plain,(
% 3.86/0.99    v2_pre_topc(sK2)),
% 3.86/0.99    inference(cnf_transformation,[],[f51])).
% 3.86/0.99  
% 3.86/0.99  fof(f79,plain,(
% 3.86/0.99    ~v2_struct_0(sK2)),
% 3.86/0.99    inference(cnf_transformation,[],[f51])).
% 3.86/0.99  
% 3.86/0.99  fof(f81,plain,(
% 3.86/0.99    l1_pre_topc(sK2)),
% 3.86/0.99    inference(cnf_transformation,[],[f51])).
% 3.86/0.99  
% 3.86/0.99  fof(f6,axiom,(
% 3.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f19,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/0.99    inference(ennf_transformation,[],[f6])).
% 3.86/0.99  
% 3.86/0.99  fof(f20,plain,(
% 3.86/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/0.99    inference(flattening,[],[f19])).
% 3.86/0.99  
% 3.86/0.99  fof(f38,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/0.99    inference(nnf_transformation,[],[f20])).
% 3.86/0.99  
% 3.86/0.99  fof(f59,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f38])).
% 3.86/0.99  
% 3.86/0.99  fof(f5,axiom,(
% 3.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f18,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/0.99    inference(ennf_transformation,[],[f5])).
% 3.86/0.99  
% 3.86/0.99  fof(f58,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f18])).
% 3.86/0.99  
% 3.86/0.99  fof(f9,axiom,(
% 3.86/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f25,plain,(
% 3.86/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.86/0.99    inference(ennf_transformation,[],[f9])).
% 3.86/0.99  
% 3.86/0.99  fof(f72,plain,(
% 3.86/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f25])).
% 3.86/0.99  
% 3.86/0.99  fof(f1,axiom,(
% 3.86/0.99    v1_xboole_0(k1_xboole_0)),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f52,plain,(
% 3.86/0.99    v1_xboole_0(k1_xboole_0)),
% 3.86/0.99    inference(cnf_transformation,[],[f1])).
% 3.86/0.99  
% 3.86/0.99  fof(f10,axiom,(
% 3.86/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f26,plain,(
% 3.86/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f10])).
% 3.86/0.99  
% 3.86/0.99  fof(f27,plain,(
% 3.86/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.86/0.99    inference(flattening,[],[f26])).
% 3.86/0.99  
% 3.86/0.99  fof(f73,plain,(
% 3.86/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f27])).
% 3.86/0.99  
% 3.86/0.99  fof(f76,plain,(
% 3.86/0.99    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f31])).
% 3.86/0.99  
% 3.86/0.99  fof(f86,plain,(
% 3.86/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 3.86/0.99    inference(cnf_transformation,[],[f51])).
% 3.86/0.99  
% 3.86/0.99  fof(f85,plain,(
% 3.86/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 3.86/0.99    inference(cnf_transformation,[],[f51])).
% 3.86/0.99  
% 3.86/0.99  fof(f8,axiom,(
% 3.86/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,X1) <=> (! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f23,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f8])).
% 3.86/0.99  
% 3.86/0.99  fof(f24,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.86/0.99    inference(flattening,[],[f23])).
% 3.86/0.99  
% 3.86/0.99  fof(f43,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) & ((! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.86/0.99    inference(nnf_transformation,[],[f24])).
% 3.86/0.99  
% 3.86/0.99  fof(f44,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.86/0.99    inference(flattening,[],[f43])).
% 3.86/0.99  
% 3.86/0.99  fof(f45,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.86/0.99    inference(rectify,[],[f44])).
% 3.86/0.99  
% 3.86/0.99  fof(f46,plain,(
% 3.86/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f47,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 3.86/0.99  
% 3.86/0.99  fof(f70,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f47])).
% 3.86/0.99  
% 3.86/0.99  fof(f75,plain,(
% 3.86/0.99    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f31])).
% 3.86/0.99  
% 3.86/0.99  fof(f4,axiom,(
% 3.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f17,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/0.99    inference(ennf_transformation,[],[f4])).
% 3.86/0.99  
% 3.86/0.99  fof(f57,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f17])).
% 3.86/0.99  
% 3.86/0.99  fof(f3,axiom,(
% 3.86/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f16,plain,(
% 3.86/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.86/0.99    inference(ennf_transformation,[],[f3])).
% 3.86/0.99  
% 3.86/0.99  fof(f56,plain,(
% 3.86/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f16])).
% 3.86/0.99  
% 3.86/0.99  fof(f7,axiom,(
% 3.86/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f21,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.86/0.99    inference(ennf_transformation,[],[f7])).
% 3.86/0.99  
% 3.86/0.99  fof(f22,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.86/0.99    inference(flattening,[],[f21])).
% 3.86/0.99  
% 3.86/0.99  fof(f39,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.86/0.99    inference(nnf_transformation,[],[f22])).
% 3.86/0.99  
% 3.86/0.99  fof(f40,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.86/0.99    inference(rectify,[],[f39])).
% 3.86/0.99  
% 3.86/0.99  fof(f41,plain,(
% 3.86/0.99    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0)))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f42,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.86/0.99  
% 3.86/0.99  fof(f66,plain,(
% 3.86/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | m1_subset_1(sK0(X0,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f42])).
% 3.86/0.99  
% 3.86/0.99  fof(f65,plain,(
% 3.86/0.99    ( ! [X2,X0,X5,X3,X1] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0) | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f42])).
% 3.86/0.99  
% 3.86/0.99  fof(f11,axiom,(
% 3.86/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f28,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f11])).
% 3.86/0.99  
% 3.86/0.99  fof(f29,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.86/0.99    inference(flattening,[],[f28])).
% 3.86/0.99  
% 3.86/0.99  fof(f74,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f29])).
% 3.86/0.99  
% 3.86/0.99  fof(f82,plain,(
% 3.86/0.99    ~v2_struct_0(sK3)),
% 3.86/0.99    inference(cnf_transformation,[],[f51])).
% 3.86/0.99  
% 3.86/0.99  fof(f13,axiom,(
% 3.86/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f32,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f13])).
% 3.86/0.99  
% 3.86/0.99  fof(f33,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.86/0.99    inference(flattening,[],[f32])).
% 3.86/0.99  
% 3.86/0.99  fof(f78,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f33])).
% 3.86/0.99  
% 3.86/0.99  fof(f84,plain,(
% 3.86/0.99    v1_funct_1(sK4)),
% 3.86/0.99    inference(cnf_transformation,[],[f51])).
% 3.86/0.99  
% 3.86/0.99  fof(f68,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f47])).
% 3.86/0.99  
% 3.86/0.99  fof(f2,axiom,(
% 3.86/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f36,plain,(
% 3.86/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.99    inference(nnf_transformation,[],[f2])).
% 3.86/0.99  
% 3.86/0.99  fof(f37,plain,(
% 3.86/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.99    inference(flattening,[],[f36])).
% 3.86/0.99  
% 3.86/0.99  fof(f53,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.86/0.99    inference(cnf_transformation,[],[f37])).
% 3.86/0.99  
% 3.86/0.99  fof(f90,plain,(
% 3.86/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.86/0.99    inference(equality_resolution,[],[f53])).
% 3.86/0.99  
% 3.86/0.99  fof(f55,plain,(
% 3.86/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f37])).
% 3.86/0.99  
% 3.86/0.99  fof(f67,plain,(
% 3.86/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f42])).
% 3.86/0.99  
% 3.86/0.99  fof(f88,plain,(
% 3.86/0.99    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4)),
% 3.86/0.99    inference(cnf_transformation,[],[f51])).
% 3.86/0.99  
% 3.86/0.99  fof(f69,plain,(
% 3.86/0.99    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_tarski(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f47])).
% 3.86/0.99  
% 3.86/0.99  fof(f71,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f47])).
% 3.86/0.99  
% 3.86/0.99  fof(f87,plain,(
% 3.86/0.99    ( ! [X3] : (k1_funct_1(sK4,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK2))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f51])).
% 3.86/0.99  
% 3.86/0.99  cnf(c_32,negated_conjecture,
% 3.86/0.99      ( m1_pre_topc(sK3,sK2) ),
% 3.86/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_23,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.86/0.99      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.86/0.99      | ~ v2_pre_topc(X1)
% 3.86/0.99      | v2_struct_0(X1)
% 3.86/0.99      | ~ l1_pre_topc(X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_35,negated_conjecture,
% 3.86/0.99      ( v2_pre_topc(sK2) ),
% 3.86/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_502,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.86/0.99      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.86/0.99      | v2_struct_0(X1)
% 3.86/0.99      | ~ l1_pre_topc(X1)
% 3.86/0.99      | sK2 != X1 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_35]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_503,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.86/0.99      | m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
% 3.86/0.99      | v2_struct_0(sK2)
% 3.86/0.99      | ~ l1_pre_topc(sK2) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_502]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_36,negated_conjecture,
% 3.86/0.99      ( ~ v2_struct_0(sK2) ),
% 3.86/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_34,negated_conjecture,
% 3.86/0.99      ( l1_pre_topc(sK2) ),
% 3.86/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_507,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.86/0.99      | m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_503,c_36,c_34]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_591,plain,
% 3.86/0.99      ( m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
% 3.86/0.99      | sK2 != sK2
% 3.86/0.99      | sK3 != X0 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_507]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_592,plain,
% 3.86/0.99      ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_591]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1729,plain,
% 3.86/0.99      ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_12,plain,
% 3.86/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.86/0.99      | k1_xboole_0 = X2 ),
% 3.86/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1739,plain,
% 3.86/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.86/0.99      | k1_xboole_0 = X1
% 3.86/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.86/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3564,plain,
% 3.86/0.99      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
% 3.86/0.99      | u1_struct_0(sK2) = k1_xboole_0
% 3.86/0.99      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1729,c_1739]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1745,plain,
% 3.86/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.86/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2484,plain,
% 3.86/0.99      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(k4_tmap_1(sK2,sK3)) ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1729,c_1745]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3568,plain,
% 3.86/0.99      ( u1_struct_0(sK2) = k1_xboole_0
% 3.86/0.99      | k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
% 3.86/0.99      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.86/0.99      inference(demodulation,[status(thm)],[c_3564,c_2484]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_20,plain,
% 3.86/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_0,plain,
% 3.86/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_21,plain,
% 3.86/0.99      ( v2_struct_0(X0)
% 3.86/0.99      | ~ l1_struct_0(X0)
% 3.86/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_403,plain,
% 3.86/0.99      ( v2_struct_0(X0)
% 3.86/0.99      | ~ l1_struct_0(X0)
% 3.86/0.99      | u1_struct_0(X0) != k1_xboole_0 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_421,plain,
% 3.86/0.99      ( v2_struct_0(X0)
% 3.86/0.99      | ~ l1_pre_topc(X0)
% 3.86/0.99      | u1_struct_0(X0) != k1_xboole_0 ),
% 3.86/0.99      inference(resolution,[status(thm)],[c_20,c_403]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_535,plain,
% 3.86/0.99      ( v2_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK2 != X0 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_421,c_34]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_536,plain,
% 3.86/0.99      ( v2_struct_0(sK2) | u1_struct_0(sK2) != k1_xboole_0 ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_535]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_24,plain,
% 3.86/0.99      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 3.86/0.99      | ~ m1_pre_topc(X1,X0)
% 3.86/0.99      | ~ v2_pre_topc(X0)
% 3.86/0.99      | v2_struct_0(X0)
% 3.86/0.99      | ~ l1_pre_topc(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_439,plain,
% 3.86/0.99      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 3.86/0.99      | ~ m1_pre_topc(X1,X0)
% 3.86/0.99      | v2_struct_0(X0)
% 3.86/0.99      | ~ l1_pre_topc(X0)
% 3.86/0.99      | sK2 != X0 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_440,plain,
% 3.86/0.99      ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
% 3.86/0.99      | ~ m1_pre_topc(X0,sK2)
% 3.86/0.99      | v2_struct_0(sK2)
% 3.86/0.99      | ~ l1_pre_topc(sK2) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_439]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_444,plain,
% 3.86/0.99      ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
% 3.86/0.99      | ~ m1_pre_topc(X0,sK2) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_440,c_36,c_34]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_626,plain,
% 3.86/0.99      ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
% 3.86/0.99      | sK2 != sK2
% 3.86/0.99      | sK3 != X0 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_444]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_627,plain,
% 3.86/0.99      ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_626]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_628,plain,
% 3.86/0.99      ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_627]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5093,plain,
% 3.86/0.99      ( k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_3568,c_36,c_536,c_628]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_29,negated_conjecture,
% 3.86/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 3.86/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1733,plain,
% 3.86/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3563,plain,
% 3.86/0.99      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),sK4) = u1_struct_0(sK3)
% 3.86/0.99      | u1_struct_0(sK2) = k1_xboole_0
% 3.86/0.99      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1733,c_1739]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2367,plain,
% 3.86/0.99      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),sK4) = k1_relat_1(sK4) ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1733,c_1745]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3575,plain,
% 3.86/0.99      ( u1_struct_0(sK2) = k1_xboole_0
% 3.86/0.99      | u1_struct_0(sK3) = k1_relat_1(sK4)
% 3.86/0.99      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.86/0.99      inference(light_normalisation,[status(thm)],[c_3563,c_2367]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_30,negated_conjecture,
% 3.86/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_43,plain,
% 3.86/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3793,plain,
% 3.86/0.99      ( u1_struct_0(sK3) = k1_relat_1(sK4) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_3575,c_36,c_43,c_536]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5095,plain,
% 3.86/0.99      ( k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4) ),
% 3.86/0.99      inference(light_normalisation,[status(thm)],[c_5093,c_3793]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_17,plain,
% 3.86/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 3.86/0.99      | r1_tarski(X0,X1)
% 3.86/0.99      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.86/0.99      | ~ v1_funct_1(X1)
% 3.86/0.99      | ~ v1_funct_1(X0)
% 3.86/0.99      | ~ v1_relat_1(X1)
% 3.86/0.99      | ~ v1_relat_1(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1737,plain,
% 3.86/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.86/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.86/0.99      | v1_funct_1(X1) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X1) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5101,plain,
% 3.86/0.99      ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_5095,c_1737]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5260,plain,
% 3.86/0.99      ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.86/0.99      inference(light_normalisation,[status(thm)],[c_5101,c_5095]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_593,plain,
% 3.86/0.99      ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_25,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.86/0.99      | ~ v2_pre_topc(X1)
% 3.86/0.99      | v2_struct_0(X1)
% 3.86/0.99      | ~ l1_pre_topc(X1)
% 3.86/0.99      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_484,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.86/0.99      | v2_struct_0(X1)
% 3.86/0.99      | ~ l1_pre_topc(X1)
% 3.86/0.99      | v1_funct_1(k4_tmap_1(X1,X0))
% 3.86/0.99      | sK2 != X1 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_35]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_485,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.86/0.99      | v2_struct_0(sK2)
% 3.86/0.99      | ~ l1_pre_topc(sK2)
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,X0)) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_484]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_489,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,sK2) | v1_funct_1(k4_tmap_1(sK2,X0)) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_485,c_36,c_34]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_598,plain,
% 3.86/0.99      ( v1_funct_1(k4_tmap_1(sK2,X0)) | sK2 != sK2 | sK3 != X0 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_489]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_599,plain,
% 3.86/0.99      ( v1_funct_1(k4_tmap_1(sK2,sK3)) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_598]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_600,plain,
% 3.86/0.99      ( v1_funct_1(k4_tmap_1(sK2,sK3)) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | v1_relat_1(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2004,plain,
% 3.86/0.99      ( ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2005,plain,
% 3.86/0.99      ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_2004]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6224,plain,
% 3.86/0.99      ( v1_relat_1(X0) != iProver_top
% 3.86/0.99      | r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_5260,c_593,c_600,c_2005]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6225,plain,
% 3.86/0.99      ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_6224]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4,plain,
% 3.86/0.99      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1747,plain,
% 3.86/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.86/0.99      | m1_subset_1(X0,X1) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6235,plain,
% 3.86/0.99      ( m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),k1_relat_1(sK4)) = iProver_top
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_6225,c_1747]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_14,plain,
% 3.86/0.99      ( r2_funct_2(X0,X1,X2,X3)
% 3.86/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.86/0.99      | ~ v1_funct_2(X3,X0,X1)
% 3.86/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.86/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.86/0.99      | m1_subset_1(sK0(X0,X2,X3),X0)
% 3.86/0.99      | ~ v1_funct_1(X3)
% 3.86/0.99      | ~ v1_funct_1(X2) ),
% 3.86/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_15,plain,
% 3.86/0.99      ( ~ r2_funct_2(X0,X1,X2,X3)
% 3.86/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.86/0.99      | ~ v1_funct_2(X3,X0,X1)
% 3.86/0.99      | ~ m1_subset_1(X4,X0)
% 3.86/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.86/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.86/0.99      | ~ v1_funct_1(X3)
% 3.86/0.99      | ~ v1_funct_1(X2)
% 3.86/0.99      | k1_funct_1(X3,X4) = k1_funct_1(X2,X4) ),
% 3.86/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_801,plain,
% 3.86/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.86/0.99      | ~ v1_funct_2(X3,X1,X2)
% 3.86/0.99      | ~ m1_subset_1(X4,X1)
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | m1_subset_1(sK0(X1,X0,X3),X1)
% 3.86/0.99      | ~ v1_funct_1(X3)
% 3.86/0.99      | ~ v1_funct_1(X0)
% 3.86/0.99      | k1_funct_1(X0,X4) = k1_funct_1(X3,X4) ),
% 3.86/0.99      inference(resolution,[status(thm)],[c_14,c_15]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1725,plain,
% 3.86/0.99      ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
% 3.86/0.99      | v1_funct_2(X0,X3,X4) != iProver_top
% 3.86/0.99      | v1_funct_2(X2,X3,X4) != iProver_top
% 3.86/0.99      | m1_subset_1(X1,X3) != iProver_top
% 3.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) != iProver_top
% 3.86/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) != iProver_top
% 3.86/0.99      | m1_subset_1(sK0(X3,X0,X2),X3) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3411,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
% 3.86/0.99      | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.86/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 3.86/0.99      | m1_subset_1(sK0(u1_struct_0(sK3),X1,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
% 3.86/0.99      | v1_funct_1(X1) != iProver_top
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1729,c_1725]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4903,plain,
% 3.86/0.99      ( v1_funct_1(X1) != iProver_top
% 3.86/0.99      | m1_subset_1(sK0(u1_struct_0(sK3),X1,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
% 3.86/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 3.86/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
% 3.86/0.99      | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_3411,c_600,c_628]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4904,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
% 3.86/0.99      | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.86/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 3.86/0.99      | m1_subset_1(sK0(u1_struct_0(sK3),X1,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
% 3.86/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_4903]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4909,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
% 3.86/0.99      | v1_funct_2(X1,k1_relat_1(sK4),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | m1_subset_1(X0,k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK2)))) != iProver_top
% 3.86/0.99      | m1_subset_1(sK0(k1_relat_1(sK4),X1,k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) = iProver_top
% 3.86/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.86/0.99      inference(light_normalisation,[status(thm)],[c_4904,c_3793]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6311,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(X1,sK1(k4_tmap_1(sK2,sK3),X0))
% 3.86/0.99      | v1_funct_2(X1,k1_relat_1(sK4),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK2)))) != iProver_top
% 3.86/0.99      | m1_subset_1(sK0(k1_relat_1(sK4),X1,k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) = iProver_top
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | v1_funct_1(X1) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_6235,c_4909]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_22,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.86/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 3.86/0.99      | v2_struct_0(X1)
% 3.86/0.99      | v2_struct_0(X0)
% 3.86/0.99      | ~ l1_pre_topc(X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_543,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.86/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 3.86/0.99      | v2_struct_0(X0)
% 3.86/0.99      | v2_struct_0(X1)
% 3.86/0.99      | sK2 != X1 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_544,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.86/0.99      | m1_subset_1(X1,u1_struct_0(sK2))
% 3.86/0.99      | v2_struct_0(X0)
% 3.86/0.99      | v2_struct_0(sK2) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_543]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_548,plain,
% 3.86/0.99      ( v2_struct_0(X0)
% 3.86/0.99      | m1_subset_1(X1,u1_struct_0(sK2))
% 3.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.86/0.99      | ~ m1_pre_topc(X0,sK2) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_544,c_36]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_549,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.86/0.99      | m1_subset_1(X1,u1_struct_0(sK2))
% 3.86/0.99      | v2_struct_0(X0) ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_548]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_573,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.86/0.99      | m1_subset_1(X0,u1_struct_0(sK2))
% 3.86/0.99      | v2_struct_0(X1)
% 3.86/0.99      | sK2 != sK2
% 3.86/0.99      | sK3 != X1 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_549]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_574,plain,
% 3.86/0.99      ( m1_subset_1(X0,u1_struct_0(sK2))
% 3.86/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.86/0.99      | v2_struct_0(sK3) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_573]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_33,negated_conjecture,
% 3.86/0.99      ( ~ v2_struct_0(sK3) ),
% 3.86/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_578,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.86/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_574,c_33]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_579,plain,
% 3.86/0.99      ( m1_subset_1(X0,u1_struct_0(sK2))
% 3.86/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_578]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1730,plain,
% 3.86/0.99      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 3.86/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3800,plain,
% 3.86/0.99      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 3.86/0.99      | m1_subset_1(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.86/0.99      inference(demodulation,[status(thm)],[c_3793,c_1730]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9895,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(X1,sK1(k4_tmap_1(sK2,sK3),X0))
% 3.86/0.99      | v1_funct_2(X1,k1_relat_1(sK4),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK2)))) != iProver_top
% 3.86/0.99      | m1_subset_1(sK0(k1_relat_1(sK4),X1,k4_tmap_1(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | v1_funct_1(X1) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_6311,c_3800]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_26,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.86/0.99      | ~ r2_hidden(X2,u1_struct_0(X0))
% 3.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.86/0.99      | ~ v2_pre_topc(X1)
% 3.86/0.99      | v2_struct_0(X1)
% 3.86/0.99      | v2_struct_0(X0)
% 3.86/0.99      | ~ l1_pre_topc(X1)
% 3.86/0.99      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 3.86/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_457,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.86/0.99      | ~ r2_hidden(X2,u1_struct_0(X0))
% 3.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.86/0.99      | v2_struct_0(X0)
% 3.86/0.99      | v2_struct_0(X1)
% 3.86/0.99      | ~ l1_pre_topc(X1)
% 3.86/0.99      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2
% 3.86/0.99      | sK2 != X1 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_35]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_458,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.86/0.99      | ~ r2_hidden(X1,u1_struct_0(X0))
% 3.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.86/0.99      | v2_struct_0(X0)
% 3.86/0.99      | v2_struct_0(sK2)
% 3.86/0.99      | ~ l1_pre_topc(sK2)
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,X0),X1) = X1 ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_457]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_462,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,sK2)
% 3.86/0.99      | ~ r2_hidden(X1,u1_struct_0(X0))
% 3.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.86/0.99      | v2_struct_0(X0)
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,X0),X1) = X1 ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_458,c_36,c_34]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_605,plain,
% 3.86/0.99      ( ~ r2_hidden(X0,u1_struct_0(X1))
% 3.86/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.86/0.99      | v2_struct_0(X1)
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,X1),X0) = X0
% 3.86/0.99      | sK2 != sK2
% 3.86/0.99      | sK3 != X1 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_462]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_606,plain,
% 3.86/0.99      ( ~ r2_hidden(X0,u1_struct_0(sK3))
% 3.86/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.86/0.99      | v2_struct_0(sK3)
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_605]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_610,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.86/0.99      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_606,c_33]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_611,plain,
% 3.86/0.99      ( ~ r2_hidden(X0,u1_struct_0(sK3))
% 3.86/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_610]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1727,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
% 3.86/0.99      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
% 3.86/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3799,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
% 3.86/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.86/0.99      inference(demodulation,[status(thm)],[c_3793,c_1727]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4689,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
% 3.86/0.99      | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1737,c_3799]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_31,negated_conjecture,
% 3.86/0.99      ( v1_funct_1(sK4) ),
% 3.86/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_42,plain,
% 3.86/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_44,plain,
% 3.86/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2001,plain,
% 3.86/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 3.86/0.99      | v1_relat_1(sK4) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2002,plain,
% 3.86/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_2001]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3634,plain,
% 3.86/0.99      ( m1_subset_1(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.86/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.86/0.99      | v1_funct_1(X1) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X1) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1737,c_1747]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4666,plain,
% 3.86/0.99      ( m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3634,c_3800]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5960,plain,
% 3.86/0.99      ( v1_relat_1(X0) != iProver_top
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_4689,c_42,c_44,c_2002,c_4666]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5961,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_5960]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5973,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_5095,c_5961]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_19,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1)
% 3.86/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.86/0.99      | ~ v1_funct_1(X1)
% 3.86/0.99      | ~ v1_funct_1(X0)
% 3.86/0.99      | ~ v1_relat_1(X1)
% 3.86/0.99      | ~ v1_relat_1(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2036,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,sK4)
% 3.86/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK4))
% 3.86/0.99      | ~ v1_funct_1(X0)
% 3.86/0.99      | ~ v1_funct_1(sK4)
% 3.86/0.99      | ~ v1_relat_1(X0)
% 3.86/0.99      | ~ v1_relat_1(sK4) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2110,plain,
% 3.86/0.99      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
% 3.86/0.99      | ~ r1_tarski(sK4,sK4)
% 3.86/0.99      | ~ v1_funct_1(sK4)
% 3.86/0.99      | ~ v1_relat_1(sK4) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2036]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2111,plain,
% 3.86/0.99      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) = iProver_top
% 3.86/0.99      | r1_tarski(sK4,sK4) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_2110]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3,plain,
% 3.86/0.99      ( r1_tarski(X0,X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2228,plain,
% 3.86/0.99      ( r1_tarski(sK4,sK4) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2229,plain,
% 3.86/0.99      ( r1_tarski(sK4,sK4) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_2228]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7980,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_5973,c_42,c_44,c_593,c_600,c_2002,c_2005,c_2111,
% 3.86/0.99                 c_2229]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.86/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1749,plain,
% 3.86/0.99      ( X0 = X1
% 3.86/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.86/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7988,plain,
% 3.86/0.99      ( k4_tmap_1(sK2,sK3) = sK4
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_7980,c_1749]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_13,plain,
% 3.86/0.99      ( r2_funct_2(X0,X1,X2,X3)
% 3.86/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.86/0.99      | ~ v1_funct_2(X3,X0,X1)
% 3.86/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.86/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.86/0.99      | ~ v1_funct_1(X3)
% 3.86/0.99      | ~ v1_funct_1(X2)
% 3.86/0.99      | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_27,negated_conjecture,
% 3.86/0.99      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) ),
% 3.86/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_876,plain,
% 3.86/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.86/0.99      | ~ v1_funct_2(X3,X1,X2)
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | ~ v1_funct_1(X3)
% 3.86/0.99      | ~ v1_funct_1(X0)
% 3.86/0.99      | k4_tmap_1(sK2,sK3) != X0
% 3.86/0.99      | k1_funct_1(X3,sK0(X1,X0,X3)) != k1_funct_1(X0,sK0(X1,X0,X3))
% 3.86/0.99      | u1_struct_0(sK2) != X2
% 3.86/0.99      | u1_struct_0(sK3) != X1
% 3.86/0.99      | sK4 != X3 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_877,plain,
% 3.86/0.99      ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
% 3.86/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
% 3.86/0.99      | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 3.86/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 3.86/0.99      | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
% 3.86/0.99      | ~ v1_funct_1(sK4)
% 3.86/0.99      | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_876]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1245,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2028,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != X0
% 3.86/0.99      | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != X0
% 3.86/0.99      | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1245]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2288,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != k1_funct_1(X0,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4))
% 3.86/0.99      | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != k1_funct_1(X0,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4))
% 3.86/0.99      | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2028]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2850,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4))
% 3.86/0.99      | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4))
% 3.86/0.99      | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2288]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1244,plain,( X0 = X0 ),theory(equality) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2851,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1244]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1254,plain,
% 3.86/0.99      ( X0 != X1 | X2 != X3 | k1_funct_1(X0,X2) = k1_funct_1(X1,X3) ),
% 3.86/0.99      theory(equality) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4054,plain,
% 3.86/0.99      ( sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) != sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | k4_tmap_1(sK2,sK3) != sK4
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1254]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4423,plain,
% 3.86/0.99      ( sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) = sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1244]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8143,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_7988,c_31,c_30,c_29,c_592,c_599,c_627,c_877,c_2850,
% 3.86/0.99                 c_2851,c_4054,c_4423]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11029,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(X0,sK1(k4_tmap_1(sK2,sK3),sK4))
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | v1_funct_2(X0,k1_relat_1(sK4),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK2)))) != iProver_top
% 3.86/0.99      | m1_subset_1(sK0(k1_relat_1(sK4),X0,k4_tmap_1(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_9895,c_8143]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1748,plain,
% 3.86/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6237,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 3.86/0.99      | m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_6225,c_3799]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6312,plain,
% 3.86/0.99      ( m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) = iProver_top
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_6235,c_3800]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6751,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_6237,c_6312]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6762,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1748,c_6751]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7229,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_6762,c_42,c_44,c_2002]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_18,plain,
% 3.86/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.86/0.99      | ~ r1_tarski(X1,X2)
% 3.86/0.99      | ~ v1_funct_1(X2)
% 3.86/0.99      | ~ v1_funct_1(X1)
% 3.86/0.99      | ~ v1_relat_1(X2)
% 3.86/0.99      | ~ v1_relat_1(X1)
% 3.86/0.99      | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1736,plain,
% 3.86/0.99      ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
% 3.86/0.99      | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
% 3.86/0.99      | r1_tarski(X2,X0) != iProver_top
% 3.86/0.99      | v1_funct_1(X2) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X2) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5098,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
% 3.86/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
% 3.86/0.99      | v1_funct_1(X1) != iProver_top
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_relat_1(X1) != iProver_top
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_5095,c_1736]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5743,plain,
% 3.86/0.99      ( v1_relat_1(X1) != iProver_top
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
% 3.86/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
% 3.86/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_5098,c_593,c_600,c_2005]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5744,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
% 3.86/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
% 3.86/0.99      | v1_funct_1(X1) != iProver_top
% 3.86/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_5743]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7240,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_7229,c_5744]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11963,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_7240,c_42,c_44,c_2002]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11972,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1737,c_11963]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_12092,plain,
% 3.86/0.99      ( v1_relat_1(X0) != iProver_top
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_11972,c_42,c_44,c_2002]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_12093,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_12092]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_12107,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_5095,c_12093]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_16,plain,
% 3.86/0.99      ( r1_tarski(X0,X1)
% 3.86/0.99      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.86/0.99      | ~ v1_funct_1(X1)
% 3.86/0.99      | ~ v1_funct_1(X0)
% 3.86/0.99      | ~ v1_relat_1(X1)
% 3.86/0.99      | ~ v1_relat_1(X0)
% 3.86/0.99      | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2508,plain,
% 3.86/0.99      ( r1_tarski(X0,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(k4_tmap_1(sK2,sK3)))
% 3.86/0.99      | ~ v1_funct_1(X0)
% 3.86/0.99      | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
% 3.86/0.99      | ~ v1_relat_1(X0)
% 3.86/0.99      | ~ v1_relat_1(k4_tmap_1(sK2,sK3))
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(X0,k4_tmap_1(sK2,sK3))) != k1_funct_1(X0,sK1(X0,k4_tmap_1(sK2,sK3))) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3606,plain,
% 3.86/0.99      ( ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
% 3.86/0.99      | ~ v1_funct_1(sK4)
% 3.86/0.99      | ~ v1_relat_1(k4_tmap_1(sK2,sK3))
% 3.86/0.99      | ~ v1_relat_1(sK4)
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) != k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2508]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3607,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) != k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_3606]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4470,plain,
% 3.86/0.99      ( k1_relat_1(sK4) = k1_relat_1(sK4) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1244]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1246,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.86/0.99      theory(equality) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3695,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1)
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
% 3.86/0.99      | k1_relat_1(k4_tmap_1(sK2,sK3)) != X1
% 3.86/0.99      | k1_relat_1(sK4) != X0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1246]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4469,plain,
% 3.86/0.99      ( ~ r1_tarski(k1_relat_1(sK4),X0)
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
% 3.86/0.99      | k1_relat_1(k4_tmap_1(sK2,sK3)) != X0
% 3.86/0.99      | k1_relat_1(sK4) != k1_relat_1(sK4) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_3695]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6994,plain,
% 3.86/0.99      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
% 3.86/0.99      | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
% 3.86/0.99      | k1_relat_1(k4_tmap_1(sK2,sK3)) != k1_relat_1(sK4)
% 3.86/0.99      | k1_relat_1(sK4) != k1_relat_1(sK4) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_4469]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6995,plain,
% 3.86/0.99      ( k1_relat_1(k4_tmap_1(sK2,sK3)) != k1_relat_1(sK4)
% 3.86/0.99      | k1_relat_1(sK4) != k1_relat_1(sK4)
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_6994]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7237,plain,
% 3.86/0.99      ( k4_tmap_1(sK2,sK3) = sK4
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_7229,c_1749]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7276,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_7237,c_31,c_30,c_29,c_592,c_599,c_627,c_877,c_2850,
% 3.86/0.99                 c_2851,c_4054,c_4423]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_12998,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_12107,c_42,c_44,c_593,c_600,c_2002,c_2005,c_2111,
% 3.86/0.99                 c_2229,c_3607,c_4470,c_5095,c_6995,c_7276]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1738,plain,
% 3.86/0.99      ( k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 3.86/0.99      | r1_tarski(X1,X0) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_funct_1(X1) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_13018,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_12998,c_1738]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_28,negated_conjecture,
% 3.86/0.99      ( ~ r2_hidden(X0,u1_struct_0(sK3))
% 3.86/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.86/0.99      | k1_funct_1(sK4,X0) = X0 ),
% 3.86/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1734,plain,
% 3.86/0.99      ( k1_funct_1(sK4,X0) = X0
% 3.86/0.99      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
% 3.86/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3806,plain,
% 3.86/0.99      ( k1_funct_1(sK4,X0) = X0
% 3.86/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.86/0.99      inference(demodulation,[status(thm)],[c_3793,c_1734]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6238,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 3.86/0.99      | m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_6225,c_3806]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6412,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_6238,c_6312]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6423,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1748,c_6412]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6458,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_6423,c_42,c_44,c_2002]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6469,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
% 3.86/0.99      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_6458,c_5744]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7686,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
% 3.86/0.99      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_6469,c_42,c_44,c_2002]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7695,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 3.86/0.99      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1737,c_7686]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9200,plain,
% 3.86/0.99      ( v1_relat_1(X0) != iProver_top
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 3.86/0.99      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_7695,c_42,c_44,c_2002]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9201,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 3.86/0.99      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_9200]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9215,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
% 3.86/0.99      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_5095,c_9201]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6466,plain,
% 3.86/0.99      ( k4_tmap_1(sK2,sK3) = sK4
% 3.86/0.99      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_6458,c_1749]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7122,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_6466,c_31,c_30,c_29,c_592,c_599,c_627,c_877,c_2850,
% 3.86/0.99                 c_2851,c_4054,c_4423]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7124,plain,
% 3.86/0.99      ( ~ r1_tarski(sK4,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
% 3.86/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_7122]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9233,plain,
% 3.86/0.99      ( ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
% 3.86/0.99      | ~ v1_relat_1(k4_tmap_1(sK2,sK3))
% 3.86/0.99      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
% 3.86/0.99      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
% 3.86/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_9215]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9696,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_9215,c_31,c_42,c_29,c_44,c_592,c_593,c_599,c_600,
% 3.86/0.99                 c_2001,c_2002,c_2004,c_2005,c_2110,c_2111,c_2228,c_2229,
% 3.86/0.99                 c_3607,c_4470,c_5095,c_6995,c_7122,c_7124,c_9233]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_13019,plain,
% 3.86/0.99      ( sK1(k4_tmap_1(sK2,sK3),sK4) != sK1(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(light_normalisation,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_13018,c_5095,c_9696]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_13020,plain,
% 3.86/0.99      ( r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(equality_resolution_simp,[status(thm)],[c_13019]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_13023,plain,
% 3.86/0.99      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_11029,c_31,c_42,c_30,c_29,c_44,c_592,c_593,c_599,
% 3.86/0.99                 c_600,c_627,c_877,c_2002,c_2005,c_2111,c_2229,c_2850,
% 3.86/0.99                 c_2851,c_4054,c_4423,c_7988,c_13020]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_13074,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) != sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_13023,c_1738]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_13075,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) != sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(light_normalisation,[status(thm)],[c_13074,c_5095]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2094,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11925,plain,
% 3.86/0.99      ( ~ r1_tarski(k4_tmap_1(sK2,sK3),sK4)
% 3.86/0.99      | ~ r1_tarski(sK4,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | k4_tmap_1(sK2,sK3) = sK4 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2094]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11926,plain,
% 3.86/0.99      ( k4_tmap_1(sK2,sK3) = sK4
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_11925]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5893,plain,
% 3.86/0.99      ( v1_relat_1(X0) != iProver_top
% 3.86/0.99      | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_4666,c_42,c_44,c_2002]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5894,plain,
% 3.86/0.99      ( m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_5893]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3979,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
% 3.86/0.99      | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_funct_1(sK4) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1737,c_3806]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4188,plain,
% 3.86/0.99      ( v1_relat_1(X0) != iProver_top
% 3.86/0.99      | k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
% 3.86/0.99      | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_3979,c_42,c_44,c_2002]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4189,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
% 3.86/0.99      | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_4188]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5904,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_5894,c_4189]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5916,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 3.86/0.99      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 3.86/0.99      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_5095,c_5904]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7770,plain,
% 3.86/0.99      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_5916,c_42,c_44,c_593,c_600,c_2002,c_2005,c_2111,
% 3.86/0.99                 c_2229]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7778,plain,
% 3.86/0.99      ( k4_tmap_1(sK2,sK3) = sK4
% 3.86/0.99      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 3.86/0.99      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_7770,c_1749]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(contradiction,plain,
% 3.86/0.99      ( $false ),
% 3.86/0.99      inference(minisat,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_13075,c_13020,c_11926,c_7778,c_4423,c_4054,c_2851,
% 3.86/0.99                 c_2850,c_2229,c_2111,c_2005,c_2002,c_877,c_627,c_600,
% 3.86/0.99                 c_599,c_593,c_592,c_44,c_29,c_30,c_42,c_31]) ).
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  ------                               Statistics
% 3.86/0.99  
% 3.86/0.99  ------ General
% 3.86/0.99  
% 3.86/0.99  abstr_ref_over_cycles:                  0
% 3.86/0.99  abstr_ref_under_cycles:                 0
% 3.86/0.99  gc_basic_clause_elim:                   0
% 3.86/0.99  forced_gc_time:                         0
% 3.86/0.99  parsing_time:                           0.045
% 3.86/0.99  unif_index_cands_time:                  0.
% 3.86/0.99  unif_index_add_time:                    0.
% 3.86/0.99  orderings_time:                         0.
% 3.86/0.99  out_proof_time:                         0.02
% 3.86/0.99  total_time:                             0.414
% 3.86/0.99  num_of_symbols:                         57
% 3.86/0.99  num_of_terms:                           8225
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing
% 3.86/0.99  
% 3.86/0.99  num_of_splits:                          0
% 3.86/0.99  num_of_split_atoms:                     0
% 3.86/0.99  num_of_reused_defs:                     0
% 3.86/0.99  num_eq_ax_congr_red:                    22
% 3.86/0.99  num_of_sem_filtered_clauses:            1
% 3.86/0.99  num_of_subtypes:                        0
% 3.86/0.99  monotx_restored_types:                  0
% 3.86/0.99  sat_num_of_epr_types:                   0
% 3.86/0.99  sat_num_of_non_cyclic_types:            0
% 3.86/0.99  sat_guarded_non_collapsed_types:        0
% 3.86/0.99  num_pure_diseq_elim:                    0
% 3.86/0.99  simp_replaced_by:                       0
% 3.86/0.99  res_preprocessed:                       152
% 3.86/0.99  prep_upred:                             0
% 3.86/0.99  prep_unflattend:                        29
% 3.86/0.99  smt_new_axioms:                         0
% 3.86/0.99  pred_elim_cands:                        6
% 3.86/0.99  pred_elim:                              7
% 3.86/0.99  pred_elim_cl:                           7
% 3.86/0.99  pred_elim_cycles:                       10
% 3.86/0.99  merged_defs:                            0
% 3.86/0.99  merged_defs_ncl:                        0
% 3.86/0.99  bin_hyper_res:                          0
% 3.86/0.99  prep_cycles:                            4
% 3.86/0.99  pred_elim_time:                         0.014
% 3.86/0.99  splitting_time:                         0.
% 3.86/0.99  sem_filter_time:                        0.
% 3.86/0.99  monotx_time:                            0.
% 3.86/0.99  subtype_inf_time:                       0.
% 3.86/0.99  
% 3.86/0.99  ------ Problem properties
% 3.86/0.99  
% 3.86/0.99  clauses:                                29
% 3.86/0.99  conjectures:                            4
% 3.86/0.99  epr:                                    4
% 3.86/0.99  horn:                                   23
% 3.86/0.99  ground:                                 9
% 3.86/0.99  unary:                                  10
% 3.86/0.99  binary:                                 4
% 3.86/0.99  lits:                                   93
% 3.86/0.99  lits_eq:                                20
% 3.86/0.99  fd_pure:                                0
% 3.86/0.99  fd_pseudo:                              0
% 3.86/0.99  fd_cond:                                3
% 3.86/0.99  fd_pseudo_cond:                         1
% 3.86/0.99  ac_symbols:                             0
% 3.86/0.99  
% 3.86/0.99  ------ Propositional Solver
% 3.86/0.99  
% 3.86/0.99  prop_solver_calls:                      31
% 3.86/0.99  prop_fast_solver_calls:                 2394
% 3.86/0.99  smt_solver_calls:                       0
% 3.86/0.99  smt_fast_solver_calls:                  0
% 3.86/0.99  prop_num_of_clauses:                    3333
% 3.86/0.99  prop_preprocess_simplified:             7906
% 3.86/0.99  prop_fo_subsumed:                       164
% 3.86/0.99  prop_solver_time:                       0.
% 3.86/0.99  smt_solver_time:                        0.
% 3.86/0.99  smt_fast_solver_time:                   0.
% 3.86/0.99  prop_fast_solver_time:                  0.
% 3.86/0.99  prop_unsat_core_time:                   0.
% 3.86/0.99  
% 3.86/0.99  ------ QBF
% 3.86/0.99  
% 3.86/0.99  qbf_q_res:                              0
% 3.86/0.99  qbf_num_tautologies:                    0
% 3.86/0.99  qbf_prep_cycles:                        0
% 3.86/0.99  
% 3.86/0.99  ------ BMC1
% 3.86/0.99  
% 3.86/0.99  bmc1_current_bound:                     -1
% 3.86/0.99  bmc1_last_solved_bound:                 -1
% 3.86/0.99  bmc1_unsat_core_size:                   -1
% 3.86/0.99  bmc1_unsat_core_parents_size:           -1
% 3.86/0.99  bmc1_merge_next_fun:                    0
% 3.86/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.86/0.99  
% 3.86/0.99  ------ Instantiation
% 3.86/0.99  
% 3.86/0.99  inst_num_of_clauses:                    1000
% 3.86/0.99  inst_num_in_passive:                    84
% 3.86/0.99  inst_num_in_active:                     657
% 3.86/0.99  inst_num_in_unprocessed:                259
% 3.86/0.99  inst_num_of_loops:                      680
% 3.86/0.99  inst_num_of_learning_restarts:          0
% 3.86/0.99  inst_num_moves_active_passive:          17
% 3.86/0.99  inst_lit_activity:                      0
% 3.86/0.99  inst_lit_activity_moves:                0
% 3.86/0.99  inst_num_tautologies:                   0
% 3.86/0.99  inst_num_prop_implied:                  0
% 3.86/0.99  inst_num_existing_simplified:           0
% 3.86/0.99  inst_num_eq_res_simplified:             0
% 3.86/0.99  inst_num_child_elim:                    0
% 3.86/0.99  inst_num_of_dismatching_blockings:      319
% 3.86/0.99  inst_num_of_non_proper_insts:           1181
% 3.86/0.99  inst_num_of_duplicates:                 0
% 3.86/0.99  inst_inst_num_from_inst_to_res:         0
% 3.86/0.99  inst_dismatching_checking_time:         0.
% 3.86/0.99  
% 3.86/0.99  ------ Resolution
% 3.86/0.99  
% 3.86/0.99  res_num_of_clauses:                     0
% 3.86/0.99  res_num_in_passive:                     0
% 3.86/0.99  res_num_in_active:                      0
% 3.86/0.99  res_num_of_loops:                       156
% 3.86/0.99  res_forward_subset_subsumed:            172
% 3.86/0.99  res_backward_subset_subsumed:           2
% 3.86/0.99  res_forward_subsumed:                   0
% 3.86/0.99  res_backward_subsumed:                  0
% 3.86/0.99  res_forward_subsumption_resolution:     0
% 3.86/0.99  res_backward_subsumption_resolution:    0
% 3.86/0.99  res_clause_to_clause_subsumption:       3204
% 3.86/0.99  res_orphan_elimination:                 0
% 3.86/0.99  res_tautology_del:                      66
% 3.86/0.99  res_num_eq_res_simplified:              0
% 3.86/0.99  res_num_sel_changes:                    0
% 3.86/0.99  res_moves_from_active_to_pass:          0
% 3.86/0.99  
% 3.86/0.99  ------ Superposition
% 3.86/0.99  
% 3.86/0.99  sup_time_total:                         0.
% 3.86/0.99  sup_time_generating:                    0.
% 3.86/0.99  sup_time_sim_full:                      0.
% 3.86/0.99  sup_time_sim_immed:                     0.
% 3.86/0.99  
% 3.86/0.99  sup_num_of_clauses:                     153
% 3.86/0.99  sup_num_in_active:                      109
% 3.86/0.99  sup_num_in_passive:                     44
% 3.86/0.99  sup_num_of_loops:                       135
% 3.86/0.99  sup_fw_superposition:                   207
% 3.86/0.99  sup_bw_superposition:                   165
% 3.86/0.99  sup_immediate_simplified:               153
% 3.86/0.99  sup_given_eliminated:                   0
% 3.86/0.99  comparisons_done:                       0
% 3.86/0.99  comparisons_avoided:                    52
% 3.86/0.99  
% 3.86/0.99  ------ Simplifications
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  sim_fw_subset_subsumed:                 51
% 3.86/0.99  sim_bw_subset_subsumed:                 11
% 3.86/0.99  sim_fw_subsumed:                        36
% 3.86/0.99  sim_bw_subsumed:                        1
% 3.86/0.99  sim_fw_subsumption_res:                 5
% 3.86/0.99  sim_bw_subsumption_res:                 0
% 3.86/0.99  sim_tautology_del:                      18
% 3.86/0.99  sim_eq_tautology_del:                   112
% 3.86/0.99  sim_eq_res_simp:                        1
% 3.86/0.99  sim_fw_demodulated:                     7
% 3.86/0.99  sim_bw_demodulated:                     20
% 3.86/0.99  sim_light_normalised:                   65
% 3.86/0.99  sim_joinable_taut:                      0
% 3.86/0.99  sim_joinable_simp:                      0
% 3.86/0.99  sim_ac_normalised:                      0
% 3.86/0.99  sim_smt_subsumption:                    0
% 3.86/0.99  
%------------------------------------------------------------------------------
