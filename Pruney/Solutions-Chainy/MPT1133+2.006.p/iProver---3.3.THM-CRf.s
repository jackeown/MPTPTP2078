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
% DateTime   : Thu Dec  3 12:11:48 EST 2020

% Result     : Theorem 15.31s
% Output     : CNFRefutation 15.31s
% Verified   : 
% Statistics : Number of formulae       :  387 (125268 expanded)
%              Number of clauses        :  260 (26454 expanded)
%              Number of leaves         :   31 (38332 expanded)
%              Depth                    :   46
%              Number of atoms          : 1592 (1487362 expanded)
%              Number of equality atoms :  747 (157207 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f80])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f170,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f113])).

fof(f21,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f87,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK3(X0,X1),X0,X1)
        & v1_funct_1(sK3(X0,X1))
        & v4_relat_1(sK3(X0,X1),X0)
        & v1_relat_1(sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK3(X0,X1),X0,X1)
      & v1_funct_1(sK3(X0,X1))
      & v4_relat_1(sK3(X0,X1),X0)
      & v1_relat_1(sK3(X0,X1))
      & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f87])).

fof(f136,plain,(
    ! [X0,X1] : m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f88])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f114,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f78])).

fof(f110,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f140,plain,(
    ! [X0,X1] : v1_funct_2(sK3(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f88])).

fof(f30,conjecture,(
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

fof(f31,negated_conjecture,(
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
    inference(negated_conjecture,[],[f30])).

fof(f68,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f69,plain,(
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
    inference(flattening,[],[f68])).

fof(f95,plain,(
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
    inference(nnf_transformation,[],[f69])).

fof(f96,plain,(
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
    inference(flattening,[],[f95])).

fof(f100,plain,(
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
     => ( ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK8 = X2
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
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
              | ~ v5_pre_topc(sK7,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK7,X0,X1) )
            & sK7 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
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
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
                  | ~ v5_pre_topc(X2,X0,sK6) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
                  | v5_pre_topc(X2,X0,sK6) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK6))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK6)
        & v2_pre_topc(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK5,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK5,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,
    ( ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
      | ~ v5_pre_topc(sK7,sK5,sK6) )
    & ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
      | v5_pre_topc(sK7,sK5,sK6) )
    & sK7 = sK8
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    & v1_funct_1(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f96,f100,f99,f98,f97])).

fof(f164,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) ),
    inference(cnf_transformation,[],[f101])).

fof(f22,axiom,(
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

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f162,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f101])).

fof(f163,plain,(
    v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(cnf_transformation,[],[f101])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f134,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f161,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f101])).

fof(f165,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f101])).

fof(f160,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f101])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f171,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f112])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f46])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f28,axiom,(
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

fof(f64,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f93,plain,(
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
    inference(nnf_transformation,[],[f65])).

fof(f151,plain,(
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
    inference(cnf_transformation,[],[f93])).

fof(f175,plain,(
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
    inference(equality_resolution,[],[f151])).

fof(f155,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f101])).

fof(f156,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f101])).

fof(f157,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f101])).

fof(f158,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f101])).

fof(f166,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f101])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f62,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f62])).

fof(f150,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f148,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f149,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f29,axiom,(
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

fof(f66,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f67,plain,(
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
    inference(flattening,[],[f66])).

fof(f94,plain,(
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
    inference(nnf_transformation,[],[f67])).

fof(f153,plain,(
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
    inference(cnf_transformation,[],[f94])).

fof(f177,plain,(
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
    inference(equality_resolution,[],[f153])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f167,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v5_pre_topc(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f101])).

fof(f154,plain,(
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
    inference(cnf_transformation,[],[f94])).

fof(f176,plain,(
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
    inference(equality_resolution,[],[f154])).

fof(f152,plain,(
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
    inference(cnf_transformation,[],[f93])).

fof(f174,plain,(
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
    inference(equality_resolution,[],[f152])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f50])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f121,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f107,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f74])).

fof(f76,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f75,f76])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f71,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f70])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f71,f72])).

fof(f102,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f170])).

cnf(c_38,plain,
    ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_6439,plain,
    ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_7268,plain,
    ( m1_subset_1(sK3(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_6439])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_6460,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7685,plain,
    ( r1_tarski(sK3(X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7268,c_6460])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_6462,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7681,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6462,c_6460])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_6464,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9878,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7681,c_6464])).

cnf(c_10893,plain,
    ( sK3(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7685,c_9878])).

cnf(c_34,plain,
    ( v1_funct_2(sK3(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_6443,plain,
    ( v1_funct_2(sK3(X0,X1),X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_11030,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10893,c_6443])).

cnf(c_56,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) ),
    inference(cnf_transformation,[],[f164])).

cnf(c_6422,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f141])).

cnf(c_6437,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_partfun1(X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_14188,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6422,c_6437])).

cnf(c_58,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f162])).

cnf(c_73,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_57,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(cnf_transformation,[],[f163])).

cnf(c_74,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_14349,plain,
    ( v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14188,c_73,c_74])).

cnf(c_14350,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_14349])).

cnf(c_33,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f134])).

cnf(c_6444,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_14353,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
    | v4_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_14350,c_6444])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_6455,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8606,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_6422,c_6455])).

cnf(c_21,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_6454,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9255,plain,
    ( v4_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6422,c_6454])).

cnf(c_20114,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14353,c_8606,c_9255])).

cnf(c_6421,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_20214,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_20114,c_6421])).

cnf(c_59,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f161])).

cnf(c_6419,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_55,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f165])).

cnf(c_6473,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6419,c_55])).

cnf(c_14189,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
    | v1_partfun1(sK8,u1_struct_0(sK5)) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6473,c_6437])).

cnf(c_60,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f160])).

cnf(c_6418,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_6472,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6418,c_55])).

cnf(c_14207,plain,
    ( v1_partfun1(sK8,u1_struct_0(sK5)) = iProver_top
    | u1_struct_0(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14189,c_73,c_6472])).

cnf(c_14208,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | v1_partfun1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_14207])).

cnf(c_14211,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | u1_struct_0(sK5) = k1_relat_1(sK8)
    | v4_relat_1(sK8,u1_struct_0(sK5)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_14208,c_6444])).

cnf(c_9256,plain,
    ( v4_relat_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6473,c_6454])).

cnf(c_17489,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14211,c_8606,c_9256])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f171])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_6451,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13267,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_6451])).

cnf(c_18,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_172,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8608,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_6455])).

cnf(c_9257,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_6454])).

cnf(c_13282,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13267,c_172,c_8608,c_9257])).

cnf(c_13283,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13282])).

cnf(c_50,plain,
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
    inference(cnf_transformation,[],[f175])).

cnf(c_6427,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_8426,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6422,c_6427])).

cnf(c_65,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f155])).

cnf(c_66,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_64,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_67,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_63,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f157])).

cnf(c_68,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_62,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f158])).

cnf(c_69,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_54,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(cnf_transformation,[],[f166])).

cnf(c_6423,plain,
    ( v5_pre_topc(sK7,sK5,sK6) = iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_6474,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v5_pre_topc(sK8,sK5,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6423,c_55])).

cnf(c_48,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_6604,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_6605,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6604])).

cnf(c_46,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_6622,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_6623,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6622])).

cnf(c_47,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_6668,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_6669,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6668])).

cnf(c_52,plain,
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
    inference(cnf_transformation,[],[f177])).

cnf(c_6746,plain,
    ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v5_pre_topc(sK8,sK5,sK6)
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_6747,plain,
    ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v5_pre_topc(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6746])).

cnf(c_8823,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8426,c_66,c_67,c_68,c_69,c_73,c_74,c_6472,c_6474,c_6473,c_6605,c_6623,c_6669,c_6747])).

cnf(c_8824,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8823])).

cnf(c_17593,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17489,c_8824])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_6461,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8827,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6461,c_8824])).

cnf(c_53,negated_conjecture,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(cnf_transformation,[],[f167])).

cnf(c_6424,plain,
    ( v5_pre_topc(sK7,sK5,sK6) != iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_6475,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(sK8,sK5,sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6424,c_55])).

cnf(c_8912,plain,
    ( v5_pre_topc(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8827,c_6475])).

cnf(c_17591,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v5_pre_topc(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17489,c_8912])).

cnf(c_13306,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13283,c_8824])).

cnf(c_15505,plain,
    ( v5_pre_topc(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13306,c_6475])).

cnf(c_17606,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_17489,c_6473])).

cnf(c_17608,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17606,c_9])).

cnf(c_18447,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v5_pre_topc(sK8,sK5,sK6) != iProver_top
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17591,c_15505,c_17608])).

cnf(c_18448,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v5_pre_topc(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_18447])).

cnf(c_23359,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17593,c_6474,c_18448])).

cnf(c_23360,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_23359])).

cnf(c_51,plain,
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
    inference(cnf_transformation,[],[f176])).

cnf(c_6426,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_7774,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6422,c_6426])).

cnf(c_6614,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_6615,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6614])).

cnf(c_6657,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_6658,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6657])).

cnf(c_6770,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_6771,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6770])).

cnf(c_8140,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7774,c_66,c_67,c_68,c_69,c_73,c_74,c_6615,c_6658,c_6771])).

cnf(c_8141,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8140])).

cnf(c_23364,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_23360,c_8141])).

cnf(c_8144,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
    | v5_pre_topc(sK8,sK5,sK6) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6474,c_8141])).

cnf(c_13065,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v5_pre_topc(sK8,sK5,sK6)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_13066,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
    | v5_pre_topc(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13065])).

cnf(c_23926,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23364,c_66,c_67,c_68,c_69,c_73,c_6472,c_6473,c_8144,c_13066])).

cnf(c_23927,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_23926])).

cnf(c_6425,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_7167,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6422,c_6425])).

cnf(c_7386,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7167,c_66,c_67,c_68,c_69,c_73,c_74,c_6615,c_6658,c_6771])).

cnf(c_7387,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7386])).

cnf(c_49,plain,
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
    inference(cnf_transformation,[],[f174])).

cnf(c_7872,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X0)
    | v5_pre_topc(sK8,sK5,X0)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_10870,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK8,sK5,sK6)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_7872])).

cnf(c_10871,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top
    | v5_pre_topc(sK8,sK5,sK6) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10870])).

cnf(c_23930,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23927,c_66,c_67,c_68,c_69,c_73,c_6472,c_6475,c_6473,c_7387,c_10871])).

cnf(c_23935,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13283,c_23930])).

cnf(c_25328,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17489,c_23935])).

cnf(c_26551,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) != iProver_top
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25328,c_17608])).

cnf(c_26552,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_26551])).

cnf(c_26555,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_20214,c_26552])).

cnf(c_26766,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_partfun1(sK8,k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26555,c_14350])).

cnf(c_6457,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13265,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK6)))) = iProver_top
    | r1_tarski(k1_relat_1(sK8),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6473,c_6451])).

cnf(c_30,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_6445,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_13966,plain,
    ( v1_funct_2(sK8,X0,u1_struct_0(sK6)) = iProver_top
    | v1_partfun1(sK8,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK8),X0) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_13265,c_6445])).

cnf(c_15206,plain,
    ( r1_tarski(k1_relat_1(sK8),X0) != iProver_top
    | v1_partfun1(sK8,X0) != iProver_top
    | v1_funct_2(sK8,X0,u1_struct_0(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13966,c_73])).

cnf(c_15207,plain,
    ( v1_funct_2(sK8,X0,u1_struct_0(sK6)) = iProver_top
    | v1_partfun1(sK8,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK8),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15206])).

cnf(c_23936,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | r1_tarski(k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13265,c_23930])).

cnf(c_23943,plain,
    ( v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | r1_tarski(k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15207,c_23936])).

cnf(c_25815,plain,
    ( v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | v4_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6457,c_23943])).

cnf(c_27834,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26766,c_73,c_74,c_8606,c_9255,c_14188,c_25815])).

cnf(c_7683,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6422,c_6460])).

cnf(c_27903,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_27834,c_7683])).

cnf(c_27907,plain,
    ( r1_tarski(sK8,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_27903,c_9])).

cnf(c_28902,plain,
    ( sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27907,c_9878])).

cnf(c_27905,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_27834,c_6421])).

cnf(c_28398,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_27905,c_26552])).

cnf(c_28486,plain,
    ( v1_funct_2(sK8,k1_relat_1(sK8),u1_struct_0(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_28398,c_6472])).

cnf(c_46859,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_28902,c_28486])).

cnf(c_7772,plain,
    ( v5_pre_topc(k1_xboole_0,X0,X1) = iProver_top
    | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6462,c_6426])).

cnf(c_19,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_169,plain,
    ( v1_funct_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_171,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_202,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16731,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | v5_pre_topc(k1_xboole_0,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7772,c_171,c_202])).

cnf(c_16732,plain,
    ( v5_pre_topc(k1_xboole_0,X0,X1) = iProver_top
    | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16731])).

cnf(c_28525,plain,
    ( v5_pre_topc(k1_xboole_0,sK5,X0) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK5),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_28398,c_16732])).

cnf(c_28596,plain,
    ( v5_pre_topc(k1_xboole_0,sK5,X0) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28525,c_28398])).

cnf(c_39079,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK5,X0) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28596,c_66,c_67])).

cnf(c_39080,plain,
    ( v5_pre_topc(k1_xboole_0,sK5,X0) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_39079])).

cnf(c_39085,plain,
    ( v5_pre_topc(k1_xboole_0,sK5,X0) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_39080,c_28902])).

cnf(c_39089,plain,
    ( v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK5,sK6) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_27834,c_39085])).

cnf(c_27875,plain,
    ( v5_pre_topc(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27834,c_15505])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_6875,plain,
    ( r1_tarski(sK8,X0)
    | r2_hidden(sK1(sK8,X0),sK8) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6881,plain,
    ( r1_tarski(sK8,X0) = iProver_top
    | r2_hidden(sK1(sK8,X0),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6875])).

cnf(c_6883,plain,
    ( r1_tarski(sK8,k1_xboole_0) = iProver_top
    | r2_hidden(sK1(sK8,k1_xboole_0),sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6881])).

cnf(c_6876,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(X0))
    | r1_tarski(sK8,X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_7568,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(sK8))
    | r1_tarski(sK8,sK8) ),
    inference(instantiation,[status(thm)],[c_6876])).

cnf(c_7574,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK8)) != iProver_top
    | r1_tarski(sK8,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7568])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_474,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_475,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_474])).

cnf(c_587,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_475])).

cnf(c_6868,plain,
    ( ~ r1_tarski(X0,sK8)
    | ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_587])).

cnf(c_15029,plain,
    ( ~ r1_tarski(sK8,sK8)
    | ~ r2_hidden(sK1(sK8,X0),sK8)
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_6868])).

cnf(c_15030,plain,
    ( r1_tarski(sK8,sK8) != iProver_top
    | r2_hidden(sK1(sK8,X0),sK8) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15029])).

cnf(c_15032,plain,
    ( r1_tarski(sK8,sK8) != iProver_top
    | r2_hidden(sK1(sK8,k1_xboole_0),sK8) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15030])).

cnf(c_7684,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6473,c_6460])).

cnf(c_9880,plain,
    ( k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)) = sK8
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7684,c_6464])).

cnf(c_17584,plain,
    ( k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)) = sK8
    | u1_struct_0(sK5) = k1_relat_1(sK8)
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK5),k1_xboole_0),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_17489,c_9880])).

cnf(c_17616,plain,
    ( k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)) = sK8
    | u1_struct_0(sK5) = k1_relat_1(sK8)
    | r1_tarski(k1_xboole_0,sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17584,c_9])).

cnf(c_6692,plain,
    ( r1_tarski(X0,sK8)
    | r2_hidden(sK1(X0,sK8),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6698,plain,
    ( r1_tarski(X0,sK8) = iProver_top
    | r2_hidden(sK1(X0,sK8),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6692])).

cnf(c_6700,plain,
    ( r1_tarski(k1_xboole_0,sK8) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,sK8),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6698])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_7495,plain,
    ( ~ r2_hidden(sK1(X0,sK8),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7496,plain,
    ( r2_hidden(sK1(X0,sK8),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7495])).

cnf(c_7498,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK8),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7496])).

cnf(c_18827,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17616,c_202,c_6700,c_7498])).

cnf(c_18828,plain,
    ( k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)) = sK8
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(renaming,[status(thm)],[c_18827])).

cnf(c_18848,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | m1_subset_1(sK8,k1_zfmisc_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18828,c_6473])).

cnf(c_7489,plain,
    ( r1_tarski(sK8,sK8)
    | r2_hidden(sK1(sK8,sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_6692])).

cnf(c_7491,plain,
    ( r1_tarski(sK8,sK8) = iProver_top
    | r2_hidden(sK1(sK8,sK8),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7489])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_6691,plain,
    ( r1_tarski(X0,sK8)
    | ~ r2_hidden(sK1(X0,sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7490,plain,
    ( r1_tarski(sK8,sK8)
    | ~ r2_hidden(sK1(sK8,sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_6691])).

cnf(c_7493,plain,
    ( r1_tarski(sK8,sK8) = iProver_top
    | r2_hidden(sK1(sK8,sK8),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7490])).

cnf(c_7467,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK8))
    | ~ r1_tarski(X0,sK8) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_18648,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK8))
    | ~ r1_tarski(sK8,sK8) ),
    inference(instantiation,[status(thm)],[c_7467])).

cnf(c_18651,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK8)) = iProver_top
    | r1_tarski(sK8,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18648])).

cnf(c_19151,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18848,c_7491,c_7493,c_18651])).

cnf(c_27900,plain,
    ( v5_pre_topc(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top
    | r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK5),k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27834,c_8912])).

cnf(c_27910,plain,
    ( v5_pre_topc(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top
    | r1_tarski(sK8,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27900,c_9])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_6453,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_11970,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_6422,c_6453])).

cnf(c_27890,plain,
    ( v1_xboole_0(sK8) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27834,c_11970])).

cnf(c_29100,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top
    | v5_pre_topc(sK8,sK5,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27875,c_202,c_6883,c_7491,c_7493,c_15032,c_27910,c_27890])).

cnf(c_29101,plain,
    ( v5_pre_topc(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_29100])).

cnf(c_29104,plain,
    ( v5_pre_topc(k1_xboole_0,sK5,sK6) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29101,c_28398,c_28902])).

cnf(c_29105,plain,
    ( v5_pre_topc(k1_xboole_0,sK5,sK6) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29104,c_28902])).

cnf(c_29107,plain,
    ( v5_pre_topc(k1_xboole_0,sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_11030,c_29105])).

cnf(c_6428,plain,
    ( v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_9192,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6422,c_6428])).

cnf(c_9489,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9192,c_66,c_67,c_68,c_69,c_73,c_74,c_6472,c_6474,c_6473,c_6605,c_6623,c_6669,c_6747,c_8426])).

cnf(c_9490,plain,
    ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9489])).

cnf(c_9493,plain,
    ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6461,c_9490])).

cnf(c_27896,plain,
    ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top
    | r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK5),k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27834,c_9493])).

cnf(c_27913,plain,
    ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top
    | r1_tarski(sK8,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27896,c_9])).

cnf(c_29538,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top
    | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27913,c_202,c_6883,c_7491,c_7493,c_15032,c_27890])).

cnf(c_29539,plain,
    ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_29538])).

cnf(c_29542,plain,
    ( v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29539,c_28398,c_28902])).

cnf(c_29543,plain,
    ( v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29542,c_28902])).

cnf(c_13264,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) = iProver_top
    | r1_tarski(k1_relat_1(sK8),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6422,c_6451])).

cnf(c_13466,plain,
    ( v5_pre_topc(sK8,X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(sK8,X0,sK6) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) != iProver_top
    | r1_tarski(k1_relat_1(sK8),u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_13264,c_6426])).

cnf(c_17091,plain,
    ( v2_pre_topc(X0) != iProver_top
    | r1_tarski(k1_relat_1(sK8),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v5_pre_topc(sK8,X0,sK6) = iProver_top
    | v5_pre_topc(sK8,X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13466,c_68,c_69,c_73])).

cnf(c_17092,plain,
    ( v5_pre_topc(sK8,X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(sK8,X0,sK6) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) != iProver_top
    | r1_tarski(k1_relat_1(sK8),u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_17091])).

cnf(c_27872,plain,
    ( v5_pre_topc(sK8,X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(sK8,X0,sK6) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(X0),k1_xboole_0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) != iProver_top
    | r1_tarski(k1_relat_1(sK8),u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27834,c_17092])).

cnf(c_35782,plain,
    ( v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(k1_xboole_0,X0,sK6) = iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) != iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27872,c_28902])).

cnf(c_184,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_186,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_190,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_192,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_7918,plain,
    ( v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6461,c_6426])).

cnf(c_28080,plain,
    ( v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(X0,X1,sK6) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6)))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27834,c_7918])).

cnf(c_28087,plain,
    ( v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(X0,X1,sK6) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6)))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28080,c_27834])).

cnf(c_28088,plain,
    ( v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(X0,X1,sK6) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6)))) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28087,c_9])).

cnf(c_31993,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(X0,X1,sK6) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6)))) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28088,c_68,c_69])).

cnf(c_31994,plain,
    ( v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(X0,X1,sK6) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6)))) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_31993])).

cnf(c_31999,plain,
    ( v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(k1_xboole_0,X0,sK6) = iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6462,c_31994])).

cnf(c_35786,plain,
    ( v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(k1_xboole_0,X0,sK6) = iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35782,c_171,c_186,c_192,c_202,c_31999])).

cnf(c_35793,plain,
    ( v5_pre_topc(k1_xboole_0,sK5,sK6) = iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK5),k1_xboole_0) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_29543,c_35786])).

cnf(c_35802,plain,
    ( v5_pre_topc(k1_xboole_0,sK5,sK6) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),k1_xboole_0) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_35793,c_28398])).

cnf(c_35803,plain,
    ( v5_pre_topc(k1_xboole_0,sK5,sK6) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_35802,c_28902])).

cnf(c_39098,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39089,c_66,c_67,c_29107,c_35803])).

cnf(c_39099,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_39098])).

cnf(c_47043,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_46859,c_39099])).

cnf(c_47500,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_11030,c_47043])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.31/2.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.31/2.51  
% 15.31/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.31/2.51  
% 15.31/2.51  ------  iProver source info
% 15.31/2.51  
% 15.31/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.31/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.31/2.51  git: non_committed_changes: false
% 15.31/2.51  git: last_make_outside_of_git: false
% 15.31/2.51  
% 15.31/2.51  ------ 
% 15.31/2.51  
% 15.31/2.51  ------ Input Options
% 15.31/2.51  
% 15.31/2.51  --out_options                           all
% 15.31/2.51  --tptp_safe_out                         true
% 15.31/2.51  --problem_path                          ""
% 15.31/2.51  --include_path                          ""
% 15.31/2.51  --clausifier                            res/vclausify_rel
% 15.31/2.51  --clausifier_options                    ""
% 15.31/2.51  --stdin                                 false
% 15.31/2.51  --stats_out                             all
% 15.31/2.51  
% 15.31/2.51  ------ General Options
% 15.31/2.51  
% 15.31/2.51  --fof                                   false
% 15.31/2.51  --time_out_real                         305.
% 15.31/2.51  --time_out_virtual                      -1.
% 15.31/2.51  --symbol_type_check                     false
% 15.31/2.51  --clausify_out                          false
% 15.31/2.51  --sig_cnt_out                           false
% 15.31/2.51  --trig_cnt_out                          false
% 15.31/2.51  --trig_cnt_out_tolerance                1.
% 15.31/2.51  --trig_cnt_out_sk_spl                   false
% 15.31/2.51  --abstr_cl_out                          false
% 15.31/2.51  
% 15.31/2.51  ------ Global Options
% 15.31/2.51  
% 15.31/2.51  --schedule                              default
% 15.31/2.51  --add_important_lit                     false
% 15.31/2.51  --prop_solver_per_cl                    1000
% 15.31/2.51  --min_unsat_core                        false
% 15.31/2.51  --soft_assumptions                      false
% 15.31/2.51  --soft_lemma_size                       3
% 15.31/2.51  --prop_impl_unit_size                   0
% 15.31/2.51  --prop_impl_unit                        []
% 15.31/2.51  --share_sel_clauses                     true
% 15.31/2.51  --reset_solvers                         false
% 15.31/2.51  --bc_imp_inh                            [conj_cone]
% 15.31/2.51  --conj_cone_tolerance                   3.
% 15.31/2.51  --extra_neg_conj                        none
% 15.31/2.51  --large_theory_mode                     true
% 15.31/2.51  --prolific_symb_bound                   200
% 15.31/2.51  --lt_threshold                          2000
% 15.31/2.51  --clause_weak_htbl                      true
% 15.31/2.51  --gc_record_bc_elim                     false
% 15.31/2.51  
% 15.31/2.51  ------ Preprocessing Options
% 15.31/2.51  
% 15.31/2.51  --preprocessing_flag                    true
% 15.31/2.51  --time_out_prep_mult                    0.1
% 15.31/2.51  --splitting_mode                        input
% 15.31/2.51  --splitting_grd                         true
% 15.31/2.51  --splitting_cvd                         false
% 15.31/2.51  --splitting_cvd_svl                     false
% 15.31/2.51  --splitting_nvd                         32
% 15.31/2.51  --sub_typing                            true
% 15.31/2.51  --prep_gs_sim                           true
% 15.31/2.51  --prep_unflatten                        true
% 15.31/2.51  --prep_res_sim                          true
% 15.31/2.51  --prep_upred                            true
% 15.31/2.51  --prep_sem_filter                       exhaustive
% 15.31/2.51  --prep_sem_filter_out                   false
% 15.31/2.51  --pred_elim                             true
% 15.31/2.51  --res_sim_input                         true
% 15.31/2.51  --eq_ax_congr_red                       true
% 15.31/2.51  --pure_diseq_elim                       true
% 15.31/2.51  --brand_transform                       false
% 15.31/2.51  --non_eq_to_eq                          false
% 15.31/2.51  --prep_def_merge                        true
% 15.31/2.51  --prep_def_merge_prop_impl              false
% 15.31/2.51  --prep_def_merge_mbd                    true
% 15.31/2.51  --prep_def_merge_tr_red                 false
% 15.31/2.51  --prep_def_merge_tr_cl                  false
% 15.31/2.51  --smt_preprocessing                     true
% 15.31/2.51  --smt_ac_axioms                         fast
% 15.31/2.51  --preprocessed_out                      false
% 15.31/2.51  --preprocessed_stats                    false
% 15.31/2.51  
% 15.31/2.51  ------ Abstraction refinement Options
% 15.31/2.51  
% 15.31/2.51  --abstr_ref                             []
% 15.31/2.51  --abstr_ref_prep                        false
% 15.31/2.51  --abstr_ref_until_sat                   false
% 15.31/2.51  --abstr_ref_sig_restrict                funpre
% 15.31/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.31/2.51  --abstr_ref_under                       []
% 15.31/2.51  
% 15.31/2.51  ------ SAT Options
% 15.31/2.51  
% 15.31/2.51  --sat_mode                              false
% 15.31/2.51  --sat_fm_restart_options                ""
% 15.31/2.51  --sat_gr_def                            false
% 15.31/2.51  --sat_epr_types                         true
% 15.31/2.51  --sat_non_cyclic_types                  false
% 15.31/2.51  --sat_finite_models                     false
% 15.31/2.51  --sat_fm_lemmas                         false
% 15.31/2.51  --sat_fm_prep                           false
% 15.31/2.51  --sat_fm_uc_incr                        true
% 15.31/2.51  --sat_out_model                         small
% 15.31/2.51  --sat_out_clauses                       false
% 15.31/2.51  
% 15.31/2.51  ------ QBF Options
% 15.31/2.51  
% 15.31/2.51  --qbf_mode                              false
% 15.31/2.51  --qbf_elim_univ                         false
% 15.31/2.51  --qbf_dom_inst                          none
% 15.31/2.51  --qbf_dom_pre_inst                      false
% 15.31/2.51  --qbf_sk_in                             false
% 15.31/2.51  --qbf_pred_elim                         true
% 15.31/2.51  --qbf_split                             512
% 15.31/2.51  
% 15.31/2.51  ------ BMC1 Options
% 15.31/2.51  
% 15.31/2.51  --bmc1_incremental                      false
% 15.31/2.51  --bmc1_axioms                           reachable_all
% 15.31/2.51  --bmc1_min_bound                        0
% 15.31/2.51  --bmc1_max_bound                        -1
% 15.31/2.51  --bmc1_max_bound_default                -1
% 15.31/2.51  --bmc1_symbol_reachability              true
% 15.31/2.51  --bmc1_property_lemmas                  false
% 15.31/2.51  --bmc1_k_induction                      false
% 15.31/2.51  --bmc1_non_equiv_states                 false
% 15.31/2.51  --bmc1_deadlock                         false
% 15.31/2.51  --bmc1_ucm                              false
% 15.31/2.51  --bmc1_add_unsat_core                   none
% 15.31/2.51  --bmc1_unsat_core_children              false
% 15.31/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.31/2.51  --bmc1_out_stat                         full
% 15.31/2.51  --bmc1_ground_init                      false
% 15.31/2.51  --bmc1_pre_inst_next_state              false
% 15.31/2.51  --bmc1_pre_inst_state                   false
% 15.31/2.51  --bmc1_pre_inst_reach_state             false
% 15.31/2.51  --bmc1_out_unsat_core                   false
% 15.31/2.51  --bmc1_aig_witness_out                  false
% 15.31/2.51  --bmc1_verbose                          false
% 15.31/2.51  --bmc1_dump_clauses_tptp                false
% 15.31/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.31/2.51  --bmc1_dump_file                        -
% 15.31/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.31/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.31/2.51  --bmc1_ucm_extend_mode                  1
% 15.31/2.51  --bmc1_ucm_init_mode                    2
% 15.31/2.51  --bmc1_ucm_cone_mode                    none
% 15.31/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.31/2.51  --bmc1_ucm_relax_model                  4
% 15.31/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.31/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.31/2.51  --bmc1_ucm_layered_model                none
% 15.31/2.51  --bmc1_ucm_max_lemma_size               10
% 15.31/2.51  
% 15.31/2.51  ------ AIG Options
% 15.31/2.51  
% 15.31/2.51  --aig_mode                              false
% 15.31/2.51  
% 15.31/2.51  ------ Instantiation Options
% 15.31/2.51  
% 15.31/2.51  --instantiation_flag                    true
% 15.31/2.51  --inst_sos_flag                         true
% 15.31/2.51  --inst_sos_phase                        true
% 15.31/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.31/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.31/2.51  --inst_lit_sel_side                     num_symb
% 15.31/2.51  --inst_solver_per_active                1400
% 15.31/2.51  --inst_solver_calls_frac                1.
% 15.31/2.51  --inst_passive_queue_type               priority_queues
% 15.31/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.31/2.51  --inst_passive_queues_freq              [25;2]
% 15.31/2.51  --inst_dismatching                      true
% 15.31/2.51  --inst_eager_unprocessed_to_passive     true
% 15.31/2.51  --inst_prop_sim_given                   true
% 15.31/2.51  --inst_prop_sim_new                     false
% 15.31/2.51  --inst_subs_new                         false
% 15.31/2.51  --inst_eq_res_simp                      false
% 15.31/2.51  --inst_subs_given                       false
% 15.31/2.51  --inst_orphan_elimination               true
% 15.31/2.51  --inst_learning_loop_flag               true
% 15.31/2.51  --inst_learning_start                   3000
% 15.31/2.51  --inst_learning_factor                  2
% 15.31/2.51  --inst_start_prop_sim_after_learn       3
% 15.31/2.51  --inst_sel_renew                        solver
% 15.31/2.51  --inst_lit_activity_flag                true
% 15.31/2.51  --inst_restr_to_given                   false
% 15.31/2.51  --inst_activity_threshold               500
% 15.31/2.51  --inst_out_proof                        true
% 15.31/2.51  
% 15.31/2.51  ------ Resolution Options
% 15.31/2.51  
% 15.31/2.51  --resolution_flag                       true
% 15.31/2.51  --res_lit_sel                           adaptive
% 15.31/2.51  --res_lit_sel_side                      none
% 15.31/2.51  --res_ordering                          kbo
% 15.31/2.51  --res_to_prop_solver                    active
% 15.31/2.51  --res_prop_simpl_new                    false
% 15.31/2.51  --res_prop_simpl_given                  true
% 15.31/2.51  --res_passive_queue_type                priority_queues
% 15.31/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.31/2.51  --res_passive_queues_freq               [15;5]
% 15.31/2.51  --res_forward_subs                      full
% 15.31/2.51  --res_backward_subs                     full
% 15.31/2.51  --res_forward_subs_resolution           true
% 15.31/2.51  --res_backward_subs_resolution          true
% 15.31/2.51  --res_orphan_elimination                true
% 15.31/2.51  --res_time_limit                        2.
% 15.31/2.51  --res_out_proof                         true
% 15.31/2.51  
% 15.31/2.51  ------ Superposition Options
% 15.31/2.51  
% 15.31/2.51  --superposition_flag                    true
% 15.31/2.51  --sup_passive_queue_type                priority_queues
% 15.31/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.31/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.31/2.51  --demod_completeness_check              fast
% 15.31/2.51  --demod_use_ground                      true
% 15.31/2.51  --sup_to_prop_solver                    passive
% 15.31/2.51  --sup_prop_simpl_new                    true
% 15.31/2.51  --sup_prop_simpl_given                  true
% 15.31/2.51  --sup_fun_splitting                     true
% 15.31/2.51  --sup_smt_interval                      50000
% 15.31/2.51  
% 15.31/2.51  ------ Superposition Simplification Setup
% 15.31/2.51  
% 15.31/2.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.31/2.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.31/2.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.31/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.31/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.31/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.31/2.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.31/2.51  --sup_immed_triv                        [TrivRules]
% 15.31/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.51  --sup_immed_bw_main                     []
% 15.31/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.31/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.31/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.51  --sup_input_bw                          []
% 15.31/2.51  
% 15.31/2.51  ------ Combination Options
% 15.31/2.51  
% 15.31/2.51  --comb_res_mult                         3
% 15.31/2.51  --comb_sup_mult                         2
% 15.31/2.51  --comb_inst_mult                        10
% 15.31/2.51  
% 15.31/2.51  ------ Debug Options
% 15.31/2.51  
% 15.31/2.51  --dbg_backtrace                         false
% 15.31/2.51  --dbg_dump_prop_clauses                 false
% 15.31/2.51  --dbg_dump_prop_clauses_file            -
% 15.31/2.51  --dbg_out_stat                          false
% 15.31/2.51  ------ Parsing...
% 15.31/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.31/2.51  
% 15.31/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.31/2.51  
% 15.31/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.31/2.51  
% 15.31/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.31/2.51  ------ Proving...
% 15.31/2.51  ------ Problem Properties 
% 15.31/2.51  
% 15.31/2.51  
% 15.31/2.51  clauses                                 64
% 15.31/2.51  conjectures                             13
% 15.31/2.51  EPR                                     14
% 15.31/2.51  Horn                                    56
% 15.31/2.51  unary                                   21
% 15.31/2.51  binary                                  18
% 15.31/2.51  lits                                    189
% 15.31/2.51  lits eq                                 17
% 15.31/2.51  fd_pure                                 0
% 15.31/2.51  fd_pseudo                               0
% 15.31/2.51  fd_cond                                 5
% 15.31/2.51  fd_pseudo_cond                          2
% 15.31/2.51  AC symbols                              0
% 15.31/2.51  
% 15.31/2.51  ------ Schedule dynamic 5 is on 
% 15.31/2.51  
% 15.31/2.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.31/2.51  
% 15.31/2.51  
% 15.31/2.51  ------ 
% 15.31/2.51  Current options:
% 15.31/2.51  ------ 
% 15.31/2.51  
% 15.31/2.51  ------ Input Options
% 15.31/2.51  
% 15.31/2.51  --out_options                           all
% 15.31/2.51  --tptp_safe_out                         true
% 15.31/2.51  --problem_path                          ""
% 15.31/2.51  --include_path                          ""
% 15.31/2.51  --clausifier                            res/vclausify_rel
% 15.31/2.51  --clausifier_options                    ""
% 15.31/2.51  --stdin                                 false
% 15.31/2.51  --stats_out                             all
% 15.31/2.51  
% 15.31/2.51  ------ General Options
% 15.31/2.51  
% 15.31/2.51  --fof                                   false
% 15.31/2.51  --time_out_real                         305.
% 15.31/2.51  --time_out_virtual                      -1.
% 15.31/2.51  --symbol_type_check                     false
% 15.31/2.51  --clausify_out                          false
% 15.31/2.51  --sig_cnt_out                           false
% 15.31/2.51  --trig_cnt_out                          false
% 15.31/2.51  --trig_cnt_out_tolerance                1.
% 15.31/2.51  --trig_cnt_out_sk_spl                   false
% 15.31/2.51  --abstr_cl_out                          false
% 15.31/2.51  
% 15.31/2.51  ------ Global Options
% 15.31/2.51  
% 15.31/2.51  --schedule                              default
% 15.31/2.51  --add_important_lit                     false
% 15.31/2.51  --prop_solver_per_cl                    1000
% 15.31/2.51  --min_unsat_core                        false
% 15.31/2.51  --soft_assumptions                      false
% 15.31/2.51  --soft_lemma_size                       3
% 15.31/2.51  --prop_impl_unit_size                   0
% 15.31/2.51  --prop_impl_unit                        []
% 15.31/2.51  --share_sel_clauses                     true
% 15.31/2.51  --reset_solvers                         false
% 15.31/2.51  --bc_imp_inh                            [conj_cone]
% 15.31/2.51  --conj_cone_tolerance                   3.
% 15.31/2.51  --extra_neg_conj                        none
% 15.31/2.51  --large_theory_mode                     true
% 15.31/2.51  --prolific_symb_bound                   200
% 15.31/2.51  --lt_threshold                          2000
% 15.31/2.51  --clause_weak_htbl                      true
% 15.31/2.51  --gc_record_bc_elim                     false
% 15.31/2.51  
% 15.31/2.51  ------ Preprocessing Options
% 15.31/2.51  
% 15.31/2.51  --preprocessing_flag                    true
% 15.31/2.51  --time_out_prep_mult                    0.1
% 15.31/2.51  --splitting_mode                        input
% 15.31/2.51  --splitting_grd                         true
% 15.31/2.51  --splitting_cvd                         false
% 15.31/2.51  --splitting_cvd_svl                     false
% 15.31/2.51  --splitting_nvd                         32
% 15.31/2.51  --sub_typing                            true
% 15.31/2.51  --prep_gs_sim                           true
% 15.31/2.51  --prep_unflatten                        true
% 15.31/2.51  --prep_res_sim                          true
% 15.31/2.51  --prep_upred                            true
% 15.31/2.51  --prep_sem_filter                       exhaustive
% 15.31/2.51  --prep_sem_filter_out                   false
% 15.31/2.51  --pred_elim                             true
% 15.31/2.51  --res_sim_input                         true
% 15.31/2.51  --eq_ax_congr_red                       true
% 15.31/2.51  --pure_diseq_elim                       true
% 15.31/2.51  --brand_transform                       false
% 15.31/2.51  --non_eq_to_eq                          false
% 15.31/2.51  --prep_def_merge                        true
% 15.31/2.51  --prep_def_merge_prop_impl              false
% 15.31/2.51  --prep_def_merge_mbd                    true
% 15.31/2.51  --prep_def_merge_tr_red                 false
% 15.31/2.51  --prep_def_merge_tr_cl                  false
% 15.31/2.51  --smt_preprocessing                     true
% 15.31/2.51  --smt_ac_axioms                         fast
% 15.31/2.51  --preprocessed_out                      false
% 15.31/2.51  --preprocessed_stats                    false
% 15.31/2.51  
% 15.31/2.51  ------ Abstraction refinement Options
% 15.31/2.51  
% 15.31/2.51  --abstr_ref                             []
% 15.31/2.51  --abstr_ref_prep                        false
% 15.31/2.51  --abstr_ref_until_sat                   false
% 15.31/2.51  --abstr_ref_sig_restrict                funpre
% 15.31/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.31/2.51  --abstr_ref_under                       []
% 15.31/2.51  
% 15.31/2.51  ------ SAT Options
% 15.31/2.51  
% 15.31/2.51  --sat_mode                              false
% 15.31/2.51  --sat_fm_restart_options                ""
% 15.31/2.51  --sat_gr_def                            false
% 15.31/2.51  --sat_epr_types                         true
% 15.31/2.51  --sat_non_cyclic_types                  false
% 15.31/2.51  --sat_finite_models                     false
% 15.31/2.51  --sat_fm_lemmas                         false
% 15.31/2.51  --sat_fm_prep                           false
% 15.31/2.51  --sat_fm_uc_incr                        true
% 15.31/2.51  --sat_out_model                         small
% 15.31/2.51  --sat_out_clauses                       false
% 15.31/2.51  
% 15.31/2.51  ------ QBF Options
% 15.31/2.51  
% 15.31/2.51  --qbf_mode                              false
% 15.31/2.51  --qbf_elim_univ                         false
% 15.31/2.51  --qbf_dom_inst                          none
% 15.31/2.51  --qbf_dom_pre_inst                      false
% 15.31/2.51  --qbf_sk_in                             false
% 15.31/2.51  --qbf_pred_elim                         true
% 15.31/2.51  --qbf_split                             512
% 15.31/2.51  
% 15.31/2.51  ------ BMC1 Options
% 15.31/2.51  
% 15.31/2.51  --bmc1_incremental                      false
% 15.31/2.51  --bmc1_axioms                           reachable_all
% 15.31/2.51  --bmc1_min_bound                        0
% 15.31/2.51  --bmc1_max_bound                        -1
% 15.31/2.51  --bmc1_max_bound_default                -1
% 15.31/2.51  --bmc1_symbol_reachability              true
% 15.31/2.51  --bmc1_property_lemmas                  false
% 15.31/2.51  --bmc1_k_induction                      false
% 15.31/2.51  --bmc1_non_equiv_states                 false
% 15.31/2.51  --bmc1_deadlock                         false
% 15.31/2.51  --bmc1_ucm                              false
% 15.31/2.51  --bmc1_add_unsat_core                   none
% 15.31/2.51  --bmc1_unsat_core_children              false
% 15.31/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.31/2.51  --bmc1_out_stat                         full
% 15.31/2.51  --bmc1_ground_init                      false
% 15.31/2.51  --bmc1_pre_inst_next_state              false
% 15.31/2.51  --bmc1_pre_inst_state                   false
% 15.31/2.51  --bmc1_pre_inst_reach_state             false
% 15.31/2.51  --bmc1_out_unsat_core                   false
% 15.31/2.51  --bmc1_aig_witness_out                  false
% 15.31/2.51  --bmc1_verbose                          false
% 15.31/2.51  --bmc1_dump_clauses_tptp                false
% 15.31/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.31/2.51  --bmc1_dump_file                        -
% 15.31/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.31/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.31/2.51  --bmc1_ucm_extend_mode                  1
% 15.31/2.51  --bmc1_ucm_init_mode                    2
% 15.31/2.51  --bmc1_ucm_cone_mode                    none
% 15.31/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.31/2.51  --bmc1_ucm_relax_model                  4
% 15.31/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.31/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.31/2.51  --bmc1_ucm_layered_model                none
% 15.31/2.51  --bmc1_ucm_max_lemma_size               10
% 15.31/2.51  
% 15.31/2.51  ------ AIG Options
% 15.31/2.51  
% 15.31/2.51  --aig_mode                              false
% 15.31/2.51  
% 15.31/2.51  ------ Instantiation Options
% 15.31/2.51  
% 15.31/2.51  --instantiation_flag                    true
% 15.31/2.51  --inst_sos_flag                         true
% 15.31/2.51  --inst_sos_phase                        true
% 15.31/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.31/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.31/2.51  --inst_lit_sel_side                     none
% 15.31/2.51  --inst_solver_per_active                1400
% 15.31/2.51  --inst_solver_calls_frac                1.
% 15.31/2.51  --inst_passive_queue_type               priority_queues
% 15.31/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.31/2.51  --inst_passive_queues_freq              [25;2]
% 15.31/2.51  --inst_dismatching                      true
% 15.31/2.51  --inst_eager_unprocessed_to_passive     true
% 15.31/2.51  --inst_prop_sim_given                   true
% 15.31/2.51  --inst_prop_sim_new                     false
% 15.31/2.51  --inst_subs_new                         false
% 15.31/2.51  --inst_eq_res_simp                      false
% 15.31/2.51  --inst_subs_given                       false
% 15.31/2.51  --inst_orphan_elimination               true
% 15.31/2.51  --inst_learning_loop_flag               true
% 15.31/2.51  --inst_learning_start                   3000
% 15.31/2.51  --inst_learning_factor                  2
% 15.31/2.51  --inst_start_prop_sim_after_learn       3
% 15.31/2.51  --inst_sel_renew                        solver
% 15.31/2.51  --inst_lit_activity_flag                true
% 15.31/2.51  --inst_restr_to_given                   false
% 15.31/2.51  --inst_activity_threshold               500
% 15.31/2.51  --inst_out_proof                        true
% 15.31/2.51  
% 15.31/2.51  ------ Resolution Options
% 15.31/2.51  
% 15.31/2.51  --resolution_flag                       false
% 15.31/2.51  --res_lit_sel                           adaptive
% 15.31/2.51  --res_lit_sel_side                      none
% 15.31/2.51  --res_ordering                          kbo
% 15.31/2.51  --res_to_prop_solver                    active
% 15.31/2.51  --res_prop_simpl_new                    false
% 15.31/2.51  --res_prop_simpl_given                  true
% 15.31/2.51  --res_passive_queue_type                priority_queues
% 15.31/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.31/2.51  --res_passive_queues_freq               [15;5]
% 15.31/2.51  --res_forward_subs                      full
% 15.31/2.51  --res_backward_subs                     full
% 15.31/2.51  --res_forward_subs_resolution           true
% 15.31/2.51  --res_backward_subs_resolution          true
% 15.31/2.51  --res_orphan_elimination                true
% 15.31/2.51  --res_time_limit                        2.
% 15.31/2.51  --res_out_proof                         true
% 15.31/2.51  
% 15.31/2.51  ------ Superposition Options
% 15.31/2.51  
% 15.31/2.51  --superposition_flag                    true
% 15.31/2.51  --sup_passive_queue_type                priority_queues
% 15.31/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.31/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.31/2.51  --demod_completeness_check              fast
% 15.31/2.51  --demod_use_ground                      true
% 15.31/2.51  --sup_to_prop_solver                    passive
% 15.31/2.51  --sup_prop_simpl_new                    true
% 15.31/2.51  --sup_prop_simpl_given                  true
% 15.31/2.51  --sup_fun_splitting                     true
% 15.31/2.51  --sup_smt_interval                      50000
% 15.31/2.51  
% 15.31/2.51  ------ Superposition Simplification Setup
% 15.31/2.51  
% 15.31/2.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.31/2.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.31/2.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.31/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.31/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.31/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.31/2.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.31/2.51  --sup_immed_triv                        [TrivRules]
% 15.31/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.51  --sup_immed_bw_main                     []
% 15.31/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.31/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.31/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.51  --sup_input_bw                          []
% 15.31/2.51  
% 15.31/2.51  ------ Combination Options
% 15.31/2.51  
% 15.31/2.51  --comb_res_mult                         3
% 15.31/2.51  --comb_sup_mult                         2
% 15.31/2.51  --comb_inst_mult                        10
% 15.31/2.51  
% 15.31/2.51  ------ Debug Options
% 15.31/2.51  
% 15.31/2.51  --dbg_backtrace                         false
% 15.31/2.51  --dbg_dump_prop_clauses                 false
% 15.31/2.51  --dbg_dump_prop_clauses_file            -
% 15.31/2.51  --dbg_out_stat                          false
% 15.31/2.51  
% 15.31/2.51  
% 15.31/2.51  
% 15.31/2.51  
% 15.31/2.51  ------ Proving...
% 15.31/2.51  
% 15.31/2.51  
% 15.31/2.51  % SZS status Theorem for theBenchmark.p
% 15.31/2.51  
% 15.31/2.51   Resolution empty clause
% 15.31/2.51  
% 15.31/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.31/2.51  
% 15.31/2.51  fof(f5,axiom,(
% 15.31/2.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f80,plain,(
% 15.31/2.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.31/2.51    inference(nnf_transformation,[],[f5])).
% 15.31/2.51  
% 15.31/2.51  fof(f81,plain,(
% 15.31/2.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.31/2.51    inference(flattening,[],[f80])).
% 15.31/2.51  
% 15.31/2.51  fof(f113,plain,(
% 15.31/2.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 15.31/2.51    inference(cnf_transformation,[],[f81])).
% 15.31/2.51  
% 15.31/2.51  fof(f170,plain,(
% 15.31/2.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 15.31/2.51    inference(equality_resolution,[],[f113])).
% 15.31/2.51  
% 15.31/2.51  fof(f21,axiom,(
% 15.31/2.51    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f34,plain,(
% 15.31/2.51    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.31/2.51    inference(pure_predicate_removal,[],[f21])).
% 15.31/2.51  
% 15.31/2.51  fof(f87,plain,(
% 15.31/2.51    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK3(X0,X1),X0,X1) & v1_funct_1(sK3(X0,X1)) & v4_relat_1(sK3(X0,X1),X0) & v1_relat_1(sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.31/2.51    introduced(choice_axiom,[])).
% 15.31/2.51  
% 15.31/2.51  fof(f88,plain,(
% 15.31/2.51    ! [X0,X1] : (v1_funct_2(sK3(X0,X1),X0,X1) & v1_funct_1(sK3(X0,X1)) & v4_relat_1(sK3(X0,X1),X0) & v1_relat_1(sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.31/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f87])).
% 15.31/2.51  
% 15.31/2.51  fof(f136,plain,(
% 15.31/2.51    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.31/2.51    inference(cnf_transformation,[],[f88])).
% 15.31/2.51  
% 15.31/2.51  fof(f7,axiom,(
% 15.31/2.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f82,plain,(
% 15.31/2.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.31/2.51    inference(nnf_transformation,[],[f7])).
% 15.31/2.51  
% 15.31/2.51  fof(f115,plain,(
% 15.31/2.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.31/2.51    inference(cnf_transformation,[],[f82])).
% 15.31/2.51  
% 15.31/2.51  fof(f6,axiom,(
% 15.31/2.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f114,plain,(
% 15.31/2.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 15.31/2.51    inference(cnf_transformation,[],[f6])).
% 15.31/2.51  
% 15.31/2.51  fof(f4,axiom,(
% 15.31/2.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f78,plain,(
% 15.31/2.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.31/2.51    inference(nnf_transformation,[],[f4])).
% 15.31/2.51  
% 15.31/2.51  fof(f79,plain,(
% 15.31/2.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.31/2.51    inference(flattening,[],[f78])).
% 15.31/2.51  
% 15.31/2.51  fof(f110,plain,(
% 15.31/2.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f79])).
% 15.31/2.51  
% 15.31/2.51  fof(f140,plain,(
% 15.31/2.51    ( ! [X0,X1] : (v1_funct_2(sK3(X0,X1),X0,X1)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f88])).
% 15.31/2.51  
% 15.31/2.51  fof(f30,conjecture,(
% 15.31/2.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f31,negated_conjecture,(
% 15.31/2.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 15.31/2.51    inference(negated_conjecture,[],[f30])).
% 15.31/2.51  
% 15.31/2.51  fof(f68,plain,(
% 15.31/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 15.31/2.51    inference(ennf_transformation,[],[f31])).
% 15.31/2.51  
% 15.31/2.51  fof(f69,plain,(
% 15.31/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.31/2.51    inference(flattening,[],[f68])).
% 15.31/2.51  
% 15.31/2.51  fof(f95,plain,(
% 15.31/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.31/2.51    inference(nnf_transformation,[],[f69])).
% 15.31/2.51  
% 15.31/2.51  fof(f96,plain,(
% 15.31/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.31/2.51    inference(flattening,[],[f95])).
% 15.31/2.51  
% 15.31/2.51  fof(f100,plain,(
% 15.31/2.51    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK8 = X2 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK8))) )),
% 15.31/2.51    introduced(choice_axiom,[])).
% 15.31/2.51  
% 15.31/2.51  fof(f99,plain,(
% 15.31/2.51    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK7,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK7,X0,X1)) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 15.31/2.51    introduced(choice_axiom,[])).
% 15.31/2.51  
% 15.31/2.51  fof(f98,plain,(
% 15.31/2.51    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v5_pre_topc(X2,X0,sK6)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(X2,X0,sK6)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK6)) & v1_funct_1(X2)) & l1_pre_topc(sK6) & v2_pre_topc(sK6))) )),
% 15.31/2.51    introduced(choice_axiom,[])).
% 15.31/2.51  
% 15.31/2.51  fof(f97,plain,(
% 15.31/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK5,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK5,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5))),
% 15.31/2.51    introduced(choice_axiom,[])).
% 15.31/2.51  
% 15.31/2.51  fof(f101,plain,(
% 15.31/2.51    ((((~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v5_pre_topc(sK7,sK5,sK6)) & (v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6)) & sK7 = sK8 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5)),
% 15.31/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f96,f100,f99,f98,f97])).
% 15.31/2.51  
% 15.31/2.51  fof(f164,plain,(
% 15.31/2.51    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))),
% 15.31/2.51    inference(cnf_transformation,[],[f101])).
% 15.31/2.51  
% 15.31/2.51  fof(f22,axiom,(
% 15.31/2.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f54,plain,(
% 15.31/2.51    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.31/2.51    inference(ennf_transformation,[],[f22])).
% 15.31/2.51  
% 15.31/2.51  fof(f55,plain,(
% 15.31/2.51    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.31/2.51    inference(flattening,[],[f54])).
% 15.31/2.51  
% 15.31/2.51  fof(f141,plain,(
% 15.31/2.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f55])).
% 15.31/2.51  
% 15.31/2.51  fof(f162,plain,(
% 15.31/2.51    v1_funct_1(sK8)),
% 15.31/2.51    inference(cnf_transformation,[],[f101])).
% 15.31/2.51  
% 15.31/2.51  fof(f163,plain,(
% 15.31/2.51    v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))),
% 15.31/2.51    inference(cnf_transformation,[],[f101])).
% 15.31/2.51  
% 15.31/2.51  fof(f20,axiom,(
% 15.31/2.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f52,plain,(
% 15.31/2.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 15.31/2.51    inference(ennf_transformation,[],[f20])).
% 15.31/2.51  
% 15.31/2.51  fof(f53,plain,(
% 15.31/2.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.31/2.51    inference(flattening,[],[f52])).
% 15.31/2.51  
% 15.31/2.51  fof(f86,plain,(
% 15.31/2.51    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.31/2.51    inference(nnf_transformation,[],[f53])).
% 15.31/2.51  
% 15.31/2.51  fof(f134,plain,(
% 15.31/2.51    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f86])).
% 15.31/2.51  
% 15.31/2.51  fof(f12,axiom,(
% 15.31/2.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f42,plain,(
% 15.31/2.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.31/2.51    inference(ennf_transformation,[],[f12])).
% 15.31/2.51  
% 15.31/2.51  fof(f122,plain,(
% 15.31/2.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.31/2.51    inference(cnf_transformation,[],[f42])).
% 15.31/2.51  
% 15.31/2.51  fof(f13,axiom,(
% 15.31/2.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f35,plain,(
% 15.31/2.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 15.31/2.51    inference(pure_predicate_removal,[],[f13])).
% 15.31/2.51  
% 15.31/2.51  fof(f43,plain,(
% 15.31/2.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.31/2.51    inference(ennf_transformation,[],[f35])).
% 15.31/2.51  
% 15.31/2.51  fof(f123,plain,(
% 15.31/2.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.31/2.51    inference(cnf_transformation,[],[f43])).
% 15.31/2.51  
% 15.31/2.51  fof(f161,plain,(
% 15.31/2.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))),
% 15.31/2.51    inference(cnf_transformation,[],[f101])).
% 15.31/2.51  
% 15.31/2.51  fof(f165,plain,(
% 15.31/2.51    sK7 = sK8),
% 15.31/2.51    inference(cnf_transformation,[],[f101])).
% 15.31/2.51  
% 15.31/2.51  fof(f160,plain,(
% 15.31/2.51    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))),
% 15.31/2.51    inference(cnf_transformation,[],[f101])).
% 15.31/2.51  
% 15.31/2.51  fof(f112,plain,(
% 15.31/2.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 15.31/2.51    inference(cnf_transformation,[],[f81])).
% 15.31/2.51  
% 15.31/2.51  fof(f171,plain,(
% 15.31/2.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 15.31/2.51    inference(equality_resolution,[],[f112])).
% 15.31/2.51  
% 15.31/2.51  fof(f16,axiom,(
% 15.31/2.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f46,plain,(
% 15.31/2.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 15.31/2.51    inference(ennf_transformation,[],[f16])).
% 15.31/2.51  
% 15.31/2.51  fof(f47,plain,(
% 15.31/2.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 15.31/2.51    inference(flattening,[],[f46])).
% 15.31/2.51  
% 15.31/2.51  fof(f126,plain,(
% 15.31/2.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 15.31/2.51    inference(cnf_transformation,[],[f47])).
% 15.31/2.51  
% 15.31/2.51  fof(f10,axiom,(
% 15.31/2.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f40,plain,(
% 15.31/2.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 15.31/2.51    inference(ennf_transformation,[],[f10])).
% 15.31/2.51  
% 15.31/2.51  fof(f83,plain,(
% 15.31/2.51    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 15.31/2.51    inference(nnf_transformation,[],[f40])).
% 15.31/2.51  
% 15.31/2.51  fof(f119,plain,(
% 15.31/2.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f83])).
% 15.31/2.51  
% 15.31/2.51  fof(f28,axiom,(
% 15.31/2.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f64,plain,(
% 15.31/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.31/2.51    inference(ennf_transformation,[],[f28])).
% 15.31/2.51  
% 15.31/2.51  fof(f65,plain,(
% 15.31/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.31/2.51    inference(flattening,[],[f64])).
% 15.31/2.51  
% 15.31/2.51  fof(f93,plain,(
% 15.31/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.31/2.51    inference(nnf_transformation,[],[f65])).
% 15.31/2.51  
% 15.31/2.51  fof(f151,plain,(
% 15.31/2.51    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f93])).
% 15.31/2.51  
% 15.31/2.51  fof(f175,plain,(
% 15.31/2.51    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.31/2.51    inference(equality_resolution,[],[f151])).
% 15.31/2.51  
% 15.31/2.51  fof(f155,plain,(
% 15.31/2.51    v2_pre_topc(sK5)),
% 15.31/2.51    inference(cnf_transformation,[],[f101])).
% 15.31/2.51  
% 15.31/2.51  fof(f156,plain,(
% 15.31/2.51    l1_pre_topc(sK5)),
% 15.31/2.51    inference(cnf_transformation,[],[f101])).
% 15.31/2.51  
% 15.31/2.51  fof(f157,plain,(
% 15.31/2.51    v2_pre_topc(sK6)),
% 15.31/2.51    inference(cnf_transformation,[],[f101])).
% 15.31/2.51  
% 15.31/2.51  fof(f158,plain,(
% 15.31/2.51    l1_pre_topc(sK6)),
% 15.31/2.51    inference(cnf_transformation,[],[f101])).
% 15.31/2.51  
% 15.31/2.51  fof(f166,plain,(
% 15.31/2.51    v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6)),
% 15.31/2.51    inference(cnf_transformation,[],[f101])).
% 15.31/2.51  
% 15.31/2.51  fof(f27,axiom,(
% 15.31/2.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f32,plain,(
% 15.31/2.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 15.31/2.51    inference(pure_predicate_removal,[],[f27])).
% 15.31/2.51  
% 15.31/2.51  fof(f62,plain,(
% 15.31/2.51    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.31/2.51    inference(ennf_transformation,[],[f32])).
% 15.31/2.51  
% 15.31/2.51  fof(f63,plain,(
% 15.31/2.51    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.31/2.51    inference(flattening,[],[f62])).
% 15.31/2.51  
% 15.31/2.51  fof(f150,plain,(
% 15.31/2.51    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f63])).
% 15.31/2.51  
% 15.31/2.51  fof(f25,axiom,(
% 15.31/2.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f33,plain,(
% 15.31/2.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 15.31/2.51    inference(pure_predicate_removal,[],[f25])).
% 15.31/2.51  
% 15.31/2.51  fof(f60,plain,(
% 15.31/2.51    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 15.31/2.51    inference(ennf_transformation,[],[f33])).
% 15.31/2.51  
% 15.31/2.51  fof(f148,plain,(
% 15.31/2.51    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.31/2.51    inference(cnf_transformation,[],[f60])).
% 15.31/2.51  
% 15.31/2.51  fof(f26,axiom,(
% 15.31/2.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f61,plain,(
% 15.31/2.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.31/2.51    inference(ennf_transformation,[],[f26])).
% 15.31/2.51  
% 15.31/2.51  fof(f149,plain,(
% 15.31/2.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f61])).
% 15.31/2.51  
% 15.31/2.51  fof(f29,axiom,(
% 15.31/2.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f66,plain,(
% 15.31/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.31/2.51    inference(ennf_transformation,[],[f29])).
% 15.31/2.51  
% 15.31/2.51  fof(f67,plain,(
% 15.31/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.31/2.51    inference(flattening,[],[f66])).
% 15.31/2.51  
% 15.31/2.51  fof(f94,plain,(
% 15.31/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.31/2.51    inference(nnf_transformation,[],[f67])).
% 15.31/2.51  
% 15.31/2.51  fof(f153,plain,(
% 15.31/2.51    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f94])).
% 15.31/2.51  
% 15.31/2.51  fof(f177,plain,(
% 15.31/2.51    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.31/2.51    inference(equality_resolution,[],[f153])).
% 15.31/2.51  
% 15.31/2.51  fof(f116,plain,(
% 15.31/2.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f82])).
% 15.31/2.51  
% 15.31/2.51  fof(f167,plain,(
% 15.31/2.51    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v5_pre_topc(sK7,sK5,sK6)),
% 15.31/2.51    inference(cnf_transformation,[],[f101])).
% 15.31/2.51  
% 15.31/2.51  fof(f154,plain,(
% 15.31/2.51    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f94])).
% 15.31/2.51  
% 15.31/2.51  fof(f176,plain,(
% 15.31/2.51    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.31/2.51    inference(equality_resolution,[],[f154])).
% 15.31/2.51  
% 15.31/2.51  fof(f152,plain,(
% 15.31/2.51    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f93])).
% 15.31/2.51  
% 15.31/2.51  fof(f174,plain,(
% 15.31/2.51    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.31/2.51    inference(equality_resolution,[],[f152])).
% 15.31/2.51  
% 15.31/2.51  fof(f19,axiom,(
% 15.31/2.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f50,plain,(
% 15.31/2.51    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.31/2.51    inference(ennf_transformation,[],[f19])).
% 15.31/2.51  
% 15.31/2.51  fof(f51,plain,(
% 15.31/2.51    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.31/2.51    inference(flattening,[],[f50])).
% 15.31/2.51  
% 15.31/2.51  fof(f133,plain,(
% 15.31/2.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.31/2.51    inference(cnf_transformation,[],[f51])).
% 15.31/2.51  
% 15.31/2.51  fof(f11,axiom,(
% 15.31/2.51    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f41,plain,(
% 15.31/2.51    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 15.31/2.51    inference(ennf_transformation,[],[f11])).
% 15.31/2.51  
% 15.31/2.51  fof(f121,plain,(
% 15.31/2.51    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f41])).
% 15.31/2.51  
% 15.31/2.51  fof(f3,axiom,(
% 15.31/2.51    v1_xboole_0(k1_xboole_0)),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f107,plain,(
% 15.31/2.51    v1_xboole_0(k1_xboole_0)),
% 15.31/2.51    inference(cnf_transformation,[],[f3])).
% 15.31/2.51  
% 15.31/2.51  fof(f2,axiom,(
% 15.31/2.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f36,plain,(
% 15.31/2.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.31/2.51    inference(ennf_transformation,[],[f2])).
% 15.31/2.51  
% 15.31/2.51  fof(f74,plain,(
% 15.31/2.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.31/2.51    inference(nnf_transformation,[],[f36])).
% 15.31/2.51  
% 15.31/2.51  fof(f75,plain,(
% 15.31/2.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.31/2.51    inference(rectify,[],[f74])).
% 15.31/2.51  
% 15.31/2.51  fof(f76,plain,(
% 15.31/2.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 15.31/2.51    introduced(choice_axiom,[])).
% 15.31/2.51  
% 15.31/2.51  fof(f77,plain,(
% 15.31/2.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.31/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f75,f76])).
% 15.31/2.51  
% 15.31/2.51  fof(f105,plain,(
% 15.31/2.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f77])).
% 15.31/2.51  
% 15.31/2.51  fof(f9,axiom,(
% 15.31/2.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f39,plain,(
% 15.31/2.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 15.31/2.51    inference(ennf_transformation,[],[f9])).
% 15.31/2.51  
% 15.31/2.51  fof(f118,plain,(
% 15.31/2.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f39])).
% 15.31/2.51  
% 15.31/2.51  fof(f1,axiom,(
% 15.31/2.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f70,plain,(
% 15.31/2.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 15.31/2.51    inference(nnf_transformation,[],[f1])).
% 15.31/2.51  
% 15.31/2.51  fof(f71,plain,(
% 15.31/2.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 15.31/2.51    inference(rectify,[],[f70])).
% 15.31/2.51  
% 15.31/2.51  fof(f72,plain,(
% 15.31/2.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 15.31/2.51    introduced(choice_axiom,[])).
% 15.31/2.51  
% 15.31/2.51  fof(f73,plain,(
% 15.31/2.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 15.31/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f71,f72])).
% 15.31/2.51  
% 15.31/2.51  fof(f102,plain,(
% 15.31/2.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f73])).
% 15.31/2.51  
% 15.31/2.51  fof(f106,plain,(
% 15.31/2.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f77])).
% 15.31/2.51  
% 15.31/2.51  fof(f14,axiom,(
% 15.31/2.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 15.31/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.51  
% 15.31/2.51  fof(f44,plain,(
% 15.31/2.51    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 15.31/2.51    inference(ennf_transformation,[],[f14])).
% 15.31/2.51  
% 15.31/2.51  fof(f124,plain,(
% 15.31/2.51    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 15.31/2.51    inference(cnf_transformation,[],[f44])).
% 15.31/2.51  
% 15.31/2.51  cnf(c_9,plain,
% 15.31/2.51      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.31/2.51      inference(cnf_transformation,[],[f170]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_38,plain,
% 15.31/2.51      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 15.31/2.51      inference(cnf_transformation,[],[f136]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6439,plain,
% 15.31/2.51      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7268,plain,
% 15.31/2.51      ( m1_subset_1(sK3(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_9,c_6439]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_14,plain,
% 15.31/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.31/2.51      inference(cnf_transformation,[],[f115]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6460,plain,
% 15.31/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.31/2.51      | r1_tarski(X0,X1) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7685,plain,
% 15.31/2.51      ( r1_tarski(sK3(X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_7268,c_6460]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_12,plain,
% 15.31/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 15.31/2.51      inference(cnf_transformation,[],[f114]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6462,plain,
% 15.31/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7681,plain,
% 15.31/2.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6462,c_6460]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6,plain,
% 15.31/2.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 15.31/2.51      inference(cnf_transformation,[],[f110]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6464,plain,
% 15.31/2.51      ( X0 = X1
% 15.31/2.51      | r1_tarski(X1,X0) != iProver_top
% 15.31/2.51      | r1_tarski(X0,X1) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_9878,plain,
% 15.31/2.51      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_7681,c_6464]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_10893,plain,
% 15.31/2.51      ( sK3(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_7685,c_9878]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_34,plain,
% 15.31/2.51      ( v1_funct_2(sK3(X0,X1),X0,X1) ),
% 15.31/2.51      inference(cnf_transformation,[],[f140]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6443,plain,
% 15.31/2.51      ( v1_funct_2(sK3(X0,X1),X0,X1) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_11030,plain,
% 15.31/2.51      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_10893,c_6443]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_56,negated_conjecture,
% 15.31/2.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) ),
% 15.31/2.51      inference(cnf_transformation,[],[f164]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6422,plain,
% 15.31/2.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_40,plain,
% 15.31/2.51      ( ~ v1_funct_2(X0,X1,X2)
% 15.31/2.51      | v1_partfun1(X0,X1)
% 15.31/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.31/2.51      | ~ v1_funct_1(X0)
% 15.31/2.51      | k1_xboole_0 = X2 ),
% 15.31/2.51      inference(cnf_transformation,[],[f141]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6437,plain,
% 15.31/2.51      ( k1_xboole_0 = X0
% 15.31/2.51      | v1_funct_2(X1,X2,X0) != iProver_top
% 15.31/2.51      | v1_partfun1(X1,X2) = iProver_top
% 15.31/2.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 15.31/2.51      | v1_funct_1(X1) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_14188,plain,
% 15.31/2.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 15.31/2.51      | v1_funct_1(sK8) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6422,c_6437]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_58,negated_conjecture,
% 15.31/2.51      ( v1_funct_1(sK8) ),
% 15.31/2.51      inference(cnf_transformation,[],[f162]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_73,plain,
% 15.31/2.51      ( v1_funct_1(sK8) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_57,negated_conjecture,
% 15.31/2.51      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
% 15.31/2.51      inference(cnf_transformation,[],[f163]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_74,plain,
% 15.31/2.51      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_14349,plain,
% 15.31/2.51      ( v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 15.31/2.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0 ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_14188,c_73,c_74]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_14350,plain,
% 15.31/2.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.31/2.51      | v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_14349]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_33,plain,
% 15.31/2.51      ( ~ v1_partfun1(X0,X1)
% 15.31/2.51      | ~ v4_relat_1(X0,X1)
% 15.31/2.51      | ~ v1_relat_1(X0)
% 15.31/2.51      | k1_relat_1(X0) = X1 ),
% 15.31/2.51      inference(cnf_transformation,[],[f134]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6444,plain,
% 15.31/2.51      ( k1_relat_1(X0) = X1
% 15.31/2.51      | v1_partfun1(X0,X1) != iProver_top
% 15.31/2.51      | v4_relat_1(X0,X1) != iProver_top
% 15.31/2.51      | v1_relat_1(X0) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_14353,plain,
% 15.31/2.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.31/2.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
% 15.31/2.51      | v4_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 15.31/2.51      | v1_relat_1(sK8) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_14350,c_6444]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_20,plain,
% 15.31/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 15.31/2.51      inference(cnf_transformation,[],[f122]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6455,plain,
% 15.31/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.31/2.51      | v1_relat_1(X0) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_8606,plain,
% 15.31/2.51      ( v1_relat_1(sK8) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6422,c_6455]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_21,plain,
% 15.31/2.51      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 15.31/2.51      inference(cnf_transformation,[],[f123]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6454,plain,
% 15.31/2.51      ( v4_relat_1(X0,X1) = iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_9255,plain,
% 15.31/2.51      ( v4_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6422,c_6454]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_20114,plain,
% 15.31/2.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.31/2.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8) ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_14353,c_8606,c_9255]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6421,plain,
% 15.31/2.51      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_20214,plain,
% 15.31/2.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_20114,c_6421]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_59,negated_conjecture,
% 15.31/2.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
% 15.31/2.51      inference(cnf_transformation,[],[f161]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6419,plain,
% 15.31/2.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_55,negated_conjecture,
% 15.31/2.51      ( sK7 = sK8 ),
% 15.31/2.51      inference(cnf_transformation,[],[f165]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6473,plain,
% 15.31/2.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
% 15.31/2.51      inference(light_normalisation,[status(thm)],[c_6419,c_55]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_14189,plain,
% 15.31/2.51      ( u1_struct_0(sK6) = k1_xboole_0
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_partfun1(sK8,u1_struct_0(sK5)) = iProver_top
% 15.31/2.51      | v1_funct_1(sK8) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6473,c_6437]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_60,negated_conjecture,
% 15.31/2.51      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
% 15.31/2.51      inference(cnf_transformation,[],[f160]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6418,plain,
% 15.31/2.51      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6472,plain,
% 15.31/2.51      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
% 15.31/2.51      inference(light_normalisation,[status(thm)],[c_6418,c_55]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_14207,plain,
% 15.31/2.51      ( v1_partfun1(sK8,u1_struct_0(sK5)) = iProver_top
% 15.31/2.51      | u1_struct_0(sK6) = k1_xboole_0 ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_14189,c_73,c_6472]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_14208,plain,
% 15.31/2.51      ( u1_struct_0(sK6) = k1_xboole_0
% 15.31/2.51      | v1_partfun1(sK8,u1_struct_0(sK5)) = iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_14207]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_14211,plain,
% 15.31/2.51      ( u1_struct_0(sK6) = k1_xboole_0
% 15.31/2.51      | u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | v4_relat_1(sK8,u1_struct_0(sK5)) != iProver_top
% 15.31/2.51      | v1_relat_1(sK8) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_14208,c_6444]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_9256,plain,
% 15.31/2.51      ( v4_relat_1(sK8,u1_struct_0(sK5)) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6473,c_6454]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_17489,plain,
% 15.31/2.51      ( u1_struct_0(sK6) = k1_xboole_0 | u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_14211,c_8606,c_9256]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_10,plain,
% 15.31/2.51      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.31/2.51      inference(cnf_transformation,[],[f171]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_24,plain,
% 15.31/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 15.31/2.51      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 15.31/2.51      inference(cnf_transformation,[],[f126]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6451,plain,
% 15.31/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_13267,plain,
% 15.31/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_10,c_6451]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_18,plain,
% 15.31/2.51      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 15.31/2.51      inference(cnf_transformation,[],[f119]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_172,plain,
% 15.31/2.51      ( v4_relat_1(X0,X1) != iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 15.31/2.51      | v1_relat_1(X0) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_8608,plain,
% 15.31/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.31/2.51      | v1_relat_1(X0) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_9,c_6455]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_9257,plain,
% 15.31/2.51      ( v4_relat_1(X0,X1) = iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_9,c_6454]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_13282,plain,
% 15.31/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_13267,c_172,c_8608,c_9257]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_13283,plain,
% 15.31/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_13282]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_50,plain,
% 15.31/2.51      ( ~ v5_pre_topc(X0,X1,X2)
% 15.31/2.51      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 15.31/2.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.31/2.51      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 15.31/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.31/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 15.31/2.51      | ~ v2_pre_topc(X1)
% 15.31/2.51      | ~ v2_pre_topc(X2)
% 15.31/2.51      | ~ l1_pre_topc(X1)
% 15.31/2.51      | ~ l1_pre_topc(X2)
% 15.31/2.51      | ~ v1_funct_1(X0) ),
% 15.31/2.51      inference(cnf_transformation,[],[f175]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6427,plain,
% 15.31/2.51      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 15.31/2.51      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(X1) != iProver_top
% 15.31/2.51      | v2_pre_topc(X2) != iProver_top
% 15.31/2.51      | l1_pre_topc(X1) != iProver_top
% 15.31/2.51      | l1_pre_topc(X2) != iProver_top
% 15.31/2.51      | v1_funct_1(X0) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_8426,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
% 15.31/2.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK5) != iProver_top
% 15.31/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK5) != iProver_top
% 15.31/2.51      | v1_funct_1(sK8) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6422,c_6427]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_65,negated_conjecture,
% 15.31/2.51      ( v2_pre_topc(sK5) ),
% 15.31/2.51      inference(cnf_transformation,[],[f155]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_66,plain,
% 15.31/2.51      ( v2_pre_topc(sK5) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_64,negated_conjecture,
% 15.31/2.51      ( l1_pre_topc(sK5) ),
% 15.31/2.51      inference(cnf_transformation,[],[f156]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_67,plain,
% 15.31/2.51      ( l1_pre_topc(sK5) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_63,negated_conjecture,
% 15.31/2.51      ( v2_pre_topc(sK6) ),
% 15.31/2.51      inference(cnf_transformation,[],[f157]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_68,plain,
% 15.31/2.51      ( v2_pre_topc(sK6) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_62,negated_conjecture,
% 15.31/2.51      ( l1_pre_topc(sK6) ),
% 15.31/2.51      inference(cnf_transformation,[],[f158]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_69,plain,
% 15.31/2.51      ( l1_pre_topc(sK6) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_54,negated_conjecture,
% 15.31/2.51      ( v5_pre_topc(sK7,sK5,sK6)
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 15.31/2.51      inference(cnf_transformation,[],[f166]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6423,plain,
% 15.31/2.51      ( v5_pre_topc(sK7,sK5,sK6) = iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6474,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,sK5,sK6) = iProver_top ),
% 15.31/2.51      inference(light_normalisation,[status(thm)],[c_6423,c_55]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_48,plain,
% 15.31/2.51      ( ~ v2_pre_topc(X0)
% 15.31/2.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 15.31/2.51      | ~ l1_pre_topc(X0) ),
% 15.31/2.51      inference(cnf_transformation,[],[f150]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6604,plain,
% 15.31/2.51      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.31/2.51      | ~ v2_pre_topc(sK6)
% 15.31/2.51      | ~ l1_pre_topc(sK6) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_48]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6605,plain,
% 15.31/2.51      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v2_pre_topc(sK6) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK6) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_6604]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_46,plain,
% 15.31/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 15.31/2.51      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 15.31/2.51      inference(cnf_transformation,[],[f148]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6622,plain,
% 15.31/2.51      ( ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
% 15.31/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_46]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6623,plain,
% 15.31/2.51      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_6622]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_47,plain,
% 15.31/2.51      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 15.31/2.51      | ~ l1_pre_topc(X0) ),
% 15.31/2.51      inference(cnf_transformation,[],[f149]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6668,plain,
% 15.31/2.51      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
% 15.31/2.51      | ~ l1_pre_topc(sK6) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_47]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6669,plain,
% 15.31/2.51      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top
% 15.31/2.51      | l1_pre_topc(sK6) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_6668]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_52,plain,
% 15.31/2.51      ( ~ v5_pre_topc(X0,X1,X2)
% 15.31/2.51      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 15.31/2.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.31/2.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 15.31/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.31/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 15.31/2.51      | ~ v2_pre_topc(X1)
% 15.31/2.51      | ~ v2_pre_topc(X2)
% 15.31/2.51      | ~ l1_pre_topc(X1)
% 15.31/2.51      | ~ l1_pre_topc(X2)
% 15.31/2.51      | ~ v1_funct_1(X0) ),
% 15.31/2.51      inference(cnf_transformation,[],[f177]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6746,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.31/2.51      | ~ v5_pre_topc(sK8,sK5,sK6)
% 15.31/2.51      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.31/2.51      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
% 15.31/2.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
% 15.31/2.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
% 15.31/2.51      | ~ v2_pre_topc(sK6)
% 15.31/2.51      | ~ v2_pre_topc(sK5)
% 15.31/2.51      | ~ l1_pre_topc(sK6)
% 15.31/2.51      | ~ l1_pre_topc(sK5)
% 15.31/2.51      | ~ v1_funct_1(sK8) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_52]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6747,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,sK5,sK6) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK6) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK5) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK6) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK5) != iProver_top
% 15.31/2.51      | v1_funct_1(sK8) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_6746]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_8823,plain,
% 15.31/2.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_8426,c_66,c_67,c_68,c_69,c_73,c_74,c_6472,c_6474,c_6473,
% 15.31/2.51                 c_6605,c_6623,c_6669,c_6747]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_8824,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_8823]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_17593,plain,
% 15.31/2.51      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6)))))) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_17489,c_8824]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_13,plain,
% 15.31/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.31/2.51      inference(cnf_transformation,[],[f116]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6461,plain,
% 15.31/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 15.31/2.51      | r1_tarski(X0,X1) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_8827,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6461,c_8824]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_53,negated_conjecture,
% 15.31/2.51      ( ~ v5_pre_topc(sK7,sK5,sK6)
% 15.31/2.51      | ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 15.31/2.51      inference(cnf_transformation,[],[f167]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6424,plain,
% 15.31/2.51      ( v5_pre_topc(sK7,sK5,sK6) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6475,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,sK5,sK6) != iProver_top ),
% 15.31/2.51      inference(light_normalisation,[status(thm)],[c_6424,c_55]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_8912,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,sK5,sK6) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_8827,c_6475]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_17591,plain,
% 15.31/2.51      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | v5_pre_topc(sK8,sK5,sK6) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6))))) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_17489,c_8912]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_13306,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_13283,c_8824]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_15505,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,sK5,sK6) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_13306,c_6475]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_17606,plain,
% 15.31/2.51      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_xboole_0))) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_17489,c_6473]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_17608,plain,
% 15.31/2.51      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_17606,c_9]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_18447,plain,
% 15.31/2.51      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,sK5,sK6) != iProver_top
% 15.31/2.51      | u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_17591,c_15505,c_17608]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_18448,plain,
% 15.31/2.51      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | v5_pre_topc(sK8,sK5,sK6) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_18447]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_23359,plain,
% 15.31/2.51      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_17593,c_6474,c_18448]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_23360,plain,
% 15.31/2.51      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_23359]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_51,plain,
% 15.31/2.51      ( v5_pre_topc(X0,X1,X2)
% 15.31/2.51      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 15.31/2.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.31/2.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 15.31/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.31/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 15.31/2.51      | ~ v2_pre_topc(X1)
% 15.31/2.51      | ~ v2_pre_topc(X2)
% 15.31/2.51      | ~ l1_pre_topc(X1)
% 15.31/2.51      | ~ l1_pre_topc(X2)
% 15.31/2.51      | ~ v1_funct_1(X0) ),
% 15.31/2.51      inference(cnf_transformation,[],[f176]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6426,plain,
% 15.31/2.51      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 15.31/2.51      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 15.31/2.51      | v2_pre_topc(X1) != iProver_top
% 15.31/2.51      | v2_pre_topc(X2) != iProver_top
% 15.31/2.51      | l1_pre_topc(X1) != iProver_top
% 15.31/2.51      | l1_pre_topc(X2) != iProver_top
% 15.31/2.51      | v1_funct_1(X0) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7774,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK6) != iProver_top
% 15.31/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK6) != iProver_top
% 15.31/2.51      | v1_funct_1(sK8) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6422,c_6426]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6614,plain,
% 15.31/2.51      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.31/2.51      | ~ v2_pre_topc(sK5)
% 15.31/2.51      | ~ l1_pre_topc(sK5) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_48]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6615,plain,
% 15.31/2.51      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 15.31/2.51      | v2_pre_topc(sK5) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK5) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_6614]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6657,plain,
% 15.31/2.51      ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 15.31/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_46]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6658,plain,
% 15.31/2.51      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
% 15.31/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_6657]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6770,plain,
% 15.31/2.51      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 15.31/2.51      | ~ l1_pre_topc(sK5) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_47]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6771,plain,
% 15.31/2.51      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
% 15.31/2.51      | l1_pre_topc(sK5) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_6770]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_8140,plain,
% 15.31/2.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_7774,c_66,c_67,c_68,c_69,c_73,c_74,c_6615,c_6658,c_6771]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_8141,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_8140]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_23364,plain,
% 15.31/2.51      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_23360,c_8141]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_8144,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,sK5,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6474,c_8141]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_13065,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
% 15.31/2.51      | ~ v5_pre_topc(sK8,sK5,sK6)
% 15.31/2.51      | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 15.31/2.51      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
% 15.31/2.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
% 15.31/2.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
% 15.31/2.51      | ~ v2_pre_topc(sK6)
% 15.31/2.51      | ~ v2_pre_topc(sK5)
% 15.31/2.51      | ~ l1_pre_topc(sK6)
% 15.31/2.51      | ~ l1_pre_topc(sK5)
% 15.31/2.51      | ~ v1_funct_1(sK8) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_50]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_13066,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,sK5,sK6) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK6) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK5) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK6) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK5) != iProver_top
% 15.31/2.51      | v1_funct_1(sK8) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_13065]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_23926,plain,
% 15.31/2.51      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_23364,c_66,c_67,c_68,c_69,c_73,c_6472,c_6473,c_8144,c_13066]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_23927,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_23926]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6425,plain,
% 15.31/2.51      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 15.31/2.51      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 15.31/2.51      | v2_pre_topc(X1) != iProver_top
% 15.31/2.51      | v2_pre_topc(X2) != iProver_top
% 15.31/2.51      | l1_pre_topc(X1) != iProver_top
% 15.31/2.51      | l1_pre_topc(X2) != iProver_top
% 15.31/2.51      | v1_funct_1(X0) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7167,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK6) != iProver_top
% 15.31/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK6) != iProver_top
% 15.31/2.51      | v1_funct_1(sK8) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6422,c_6425]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7386,plain,
% 15.31/2.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_7167,c_66,c_67,c_68,c_69,c_73,c_74,c_6615,c_6658,c_6771]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7387,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_7386]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_49,plain,
% 15.31/2.51      ( v5_pre_topc(X0,X1,X2)
% 15.31/2.51      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 15.31/2.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.31/2.51      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 15.31/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.31/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 15.31/2.51      | ~ v2_pre_topc(X1)
% 15.31/2.51      | ~ v2_pre_topc(X2)
% 15.31/2.51      | ~ l1_pre_topc(X1)
% 15.31/2.51      | ~ l1_pre_topc(X2)
% 15.31/2.51      | ~ v1_funct_1(X0) ),
% 15.31/2.51      inference(cnf_transformation,[],[f174]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7872,plain,
% 15.31/2.51      ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X0)
% 15.31/2.51      | v5_pre_topc(sK8,sK5,X0)
% 15.31/2.51      | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))
% 15.31/2.51      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(X0))
% 15.31/2.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))))
% 15.31/2.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 15.31/2.51      | ~ v2_pre_topc(X0)
% 15.31/2.51      | ~ v2_pre_topc(sK5)
% 15.31/2.51      | ~ l1_pre_topc(X0)
% 15.31/2.51      | ~ l1_pre_topc(sK5)
% 15.31/2.51      | ~ v1_funct_1(sK8) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_49]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_10870,plain,
% 15.31/2.51      ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
% 15.31/2.51      | v5_pre_topc(sK8,sK5,sK6)
% 15.31/2.51      | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 15.31/2.51      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
% 15.31/2.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
% 15.31/2.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
% 15.31/2.51      | ~ v2_pre_topc(sK6)
% 15.31/2.51      | ~ v2_pre_topc(sK5)
% 15.31/2.51      | ~ l1_pre_topc(sK6)
% 15.31/2.51      | ~ l1_pre_topc(sK5)
% 15.31/2.51      | ~ v1_funct_1(sK8) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_7872]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_10871,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,sK5,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK6) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK5) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK6) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK5) != iProver_top
% 15.31/2.51      | v1_funct_1(sK8) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_10870]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_23930,plain,
% 15.31/2.51      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_23927,c_66,c_67,c_68,c_69,c_73,c_6472,c_6475,c_6473,
% 15.31/2.51                 c_7387,c_10871]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_23935,plain,
% 15.31/2.51      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_13283,c_23930]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_25328,plain,
% 15.31/2.51      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_17489,c_23935]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_26551,plain,
% 15.31/2.51      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) != iProver_top
% 15.31/2.51      | u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_25328,c_17608]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_26552,plain,
% 15.31/2.51      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_26551]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_26555,plain,
% 15.31/2.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
% 15.31/2.51      | u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_20214,c_26552]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_26766,plain,
% 15.31/2.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.31/2.51      | u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | v1_partfun1(sK8,k1_relat_1(sK8)) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_26555,c_14350]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6457,plain,
% 15.31/2.51      ( v4_relat_1(X0,X1) != iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 15.31/2.51      | v1_relat_1(X0) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_13265,plain,
% 15.31/2.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK6)))) = iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(sK8),X0) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6473,c_6451]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_30,plain,
% 15.31/2.51      ( v1_funct_2(X0,X1,X2)
% 15.31/2.51      | ~ v1_partfun1(X0,X1)
% 15.31/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.31/2.51      | ~ v1_funct_1(X0) ),
% 15.31/2.51      inference(cnf_transformation,[],[f133]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6445,plain,
% 15.31/2.51      ( v1_funct_2(X0,X1,X2) = iProver_top
% 15.31/2.51      | v1_partfun1(X0,X1) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.31/2.51      | v1_funct_1(X0) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_13966,plain,
% 15.31/2.51      ( v1_funct_2(sK8,X0,u1_struct_0(sK6)) = iProver_top
% 15.31/2.51      | v1_partfun1(sK8,X0) != iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(sK8),X0) != iProver_top
% 15.31/2.51      | v1_funct_1(sK8) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_13265,c_6445]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_15206,plain,
% 15.31/2.51      ( r1_tarski(k1_relat_1(sK8),X0) != iProver_top
% 15.31/2.51      | v1_partfun1(sK8,X0) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,X0,u1_struct_0(sK6)) = iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,[status(thm)],[c_13966,c_73]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_15207,plain,
% 15.31/2.51      ( v1_funct_2(sK8,X0,u1_struct_0(sK6)) = iProver_top
% 15.31/2.51      | v1_partfun1(sK8,X0) != iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(sK8),X0) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_15206]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_23936,plain,
% 15.31/2.51      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_13265,c_23930]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_23943,plain,
% 15.31/2.51      ( v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_15207,c_23936]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_25815,plain,
% 15.31/2.51      ( v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 15.31/2.51      | v4_relat_1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 15.31/2.51      | v1_relat_1(sK8) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6457,c_23943]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_27834,plain,
% 15.31/2.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0 ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_26766,c_73,c_74,c_8606,c_9255,c_14188,c_25815]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7683,plain,
% 15.31/2.51      ( r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6422,c_6460]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_27903,plain,
% 15.31/2.51      ( r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0)) = iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_27834,c_7683]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_27907,plain,
% 15.31/2.51      ( r1_tarski(sK8,k1_xboole_0) = iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_27903,c_9]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_28902,plain,
% 15.31/2.51      ( sK8 = k1_xboole_0 ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_27907,c_9878]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_27905,plain,
% 15.31/2.51      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) = iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_27834,c_6421]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_28398,plain,
% 15.31/2.51      ( u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_27905,c_26552]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_28486,plain,
% 15.31/2.51      ( v1_funct_2(sK8,k1_relat_1(sK8),u1_struct_0(sK6)) = iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_28398,c_6472]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_46859,plain,
% 15.31/2.51      ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK6)) = iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_28902,c_28486]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7772,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,X0,X1) = iProver_top
% 15.31/2.51      | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 15.31/2.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(X1) != iProver_top
% 15.31/2.51      | v2_pre_topc(X0) != iProver_top
% 15.31/2.51      | l1_pre_topc(X1) != iProver_top
% 15.31/2.51      | l1_pre_topc(X0) != iProver_top
% 15.31/2.51      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6462,c_6426]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_19,plain,
% 15.31/2.51      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 15.31/2.51      inference(cnf_transformation,[],[f121]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_169,plain,
% 15.31/2.51      ( v1_funct_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_171,plain,
% 15.31/2.51      ( v1_funct_1(k1_xboole_0) = iProver_top
% 15.31/2.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_169]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_5,plain,
% 15.31/2.51      ( v1_xboole_0(k1_xboole_0) ),
% 15.31/2.51      inference(cnf_transformation,[],[f107]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_202,plain,
% 15.31/2.51      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_16731,plain,
% 15.31/2.51      ( l1_pre_topc(X0) != iProver_top
% 15.31/2.51      | l1_pre_topc(X1) != iProver_top
% 15.31/2.51      | v2_pre_topc(X0) != iProver_top
% 15.31/2.51      | v2_pre_topc(X1) != iProver_top
% 15.31/2.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.31/2.51      | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 15.31/2.51      | v5_pre_topc(k1_xboole_0,X0,X1) = iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_7772,c_171,c_202]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_16732,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,X0,X1) = iProver_top
% 15.31/2.51      | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 15.31/2.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(X1) != iProver_top
% 15.31/2.51      | v2_pre_topc(X0) != iProver_top
% 15.31/2.51      | l1_pre_topc(X1) != iProver_top
% 15.31/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_16731]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_28525,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,sK5,X0) = iProver_top
% 15.31/2.51      | v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(sK5),u1_struct_0(X0)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 15.31/2.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(X0) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK5) != iProver_top
% 15.31/2.51      | l1_pre_topc(X0) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK5) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_28398,c_16732]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_28596,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,sK5,X0) = iProver_top
% 15.31/2.51      | v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(X0)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 15.31/2.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(X0)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(X0) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK5) != iProver_top
% 15.31/2.51      | l1_pre_topc(X0) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK5) != iProver_top ),
% 15.31/2.51      inference(light_normalisation,[status(thm)],[c_28525,c_28398]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_39079,plain,
% 15.31/2.51      ( l1_pre_topc(X0) != iProver_top
% 15.31/2.51      | v5_pre_topc(k1_xboole_0,sK5,X0) = iProver_top
% 15.31/2.51      | v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(X0)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 15.31/2.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(X0)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(X0) != iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_28596,c_66,c_67]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_39080,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,sK5,X0) = iProver_top
% 15.31/2.51      | v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(X0)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 15.31/2.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(X0)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(X0) != iProver_top
% 15.31/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_39079]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_39085,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,sK5,X0) = iProver_top
% 15.31/2.51      | v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X0)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 15.31/2.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X0)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(X0) != iProver_top
% 15.31/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.31/2.51      inference(light_normalisation,[status(thm)],[c_39080,c_28902]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_39089,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(k1_xboole_0,sK5,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 15.31/2.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK6) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK6) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_27834,c_39085]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_27875,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,sK5,sK6) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_27834,c_15505]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_3,plain,
% 15.31/2.51      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 15.31/2.51      inference(cnf_transformation,[],[f105]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6875,plain,
% 15.31/2.51      ( r1_tarski(sK8,X0) | r2_hidden(sK1(sK8,X0),sK8) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_3]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6881,plain,
% 15.31/2.51      ( r1_tarski(sK8,X0) = iProver_top
% 15.31/2.51      | r2_hidden(sK1(sK8,X0),sK8) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_6875]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6883,plain,
% 15.31/2.51      ( r1_tarski(sK8,k1_xboole_0) = iProver_top
% 15.31/2.51      | r2_hidden(sK1(sK8,k1_xboole_0),sK8) = iProver_top ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_6881]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6876,plain,
% 15.31/2.51      ( ~ m1_subset_1(sK8,k1_zfmisc_1(X0)) | r1_tarski(sK8,X0) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_14]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7568,plain,
% 15.31/2.51      ( ~ m1_subset_1(sK8,k1_zfmisc_1(sK8)) | r1_tarski(sK8,sK8) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_6876]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7574,plain,
% 15.31/2.51      ( m1_subset_1(sK8,k1_zfmisc_1(sK8)) != iProver_top
% 15.31/2.51      | r1_tarski(sK8,sK8) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_7568]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_16,plain,
% 15.31/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.31/2.51      | ~ r2_hidden(X2,X0)
% 15.31/2.51      | ~ v1_xboole_0(X1) ),
% 15.31/2.51      inference(cnf_transformation,[],[f118]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_474,plain,
% 15.31/2.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.31/2.51      inference(prop_impl,[status(thm)],[c_13]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_475,plain,
% 15.31/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_474]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_587,plain,
% 15.31/2.51      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 15.31/2.51      inference(bin_hyper_res,[status(thm)],[c_16,c_475]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6868,plain,
% 15.31/2.51      ( ~ r1_tarski(X0,sK8) | ~ r2_hidden(X1,X0) | ~ v1_xboole_0(sK8) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_587]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_15029,plain,
% 15.31/2.51      ( ~ r1_tarski(sK8,sK8)
% 15.31/2.51      | ~ r2_hidden(sK1(sK8,X0),sK8)
% 15.31/2.51      | ~ v1_xboole_0(sK8) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_6868]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_15030,plain,
% 15.31/2.51      ( r1_tarski(sK8,sK8) != iProver_top
% 15.31/2.51      | r2_hidden(sK1(sK8,X0),sK8) != iProver_top
% 15.31/2.51      | v1_xboole_0(sK8) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_15029]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_15032,plain,
% 15.31/2.51      ( r1_tarski(sK8,sK8) != iProver_top
% 15.31/2.51      | r2_hidden(sK1(sK8,k1_xboole_0),sK8) != iProver_top
% 15.31/2.51      | v1_xboole_0(sK8) != iProver_top ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_15030]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7684,plain,
% 15.31/2.51      ( r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6473,c_6460]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_9880,plain,
% 15.31/2.51      ( k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)) = sK8
% 15.31/2.51      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)),sK8) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_7684,c_6464]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_17584,plain,
% 15.31/2.51      ( k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)) = sK8
% 15.31/2.51      | u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK5),k1_xboole_0),sK8) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_17489,c_9880]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_17616,plain,
% 15.31/2.51      ( k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)) = sK8
% 15.31/2.51      | u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | r1_tarski(k1_xboole_0,sK8) != iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_17584,c_9]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6692,plain,
% 15.31/2.51      ( r1_tarski(X0,sK8) | r2_hidden(sK1(X0,sK8),X0) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_3]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6698,plain,
% 15.31/2.51      ( r1_tarski(X0,sK8) = iProver_top
% 15.31/2.51      | r2_hidden(sK1(X0,sK8),X0) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_6692]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6700,plain,
% 15.31/2.51      ( r1_tarski(k1_xboole_0,sK8) = iProver_top
% 15.31/2.51      | r2_hidden(sK1(k1_xboole_0,sK8),k1_xboole_0) = iProver_top ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_6698]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_1,plain,
% 15.31/2.51      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 15.31/2.51      inference(cnf_transformation,[],[f102]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7495,plain,
% 15.31/2.51      ( ~ r2_hidden(sK1(X0,sK8),X0) | ~ v1_xboole_0(X0) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_1]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7496,plain,
% 15.31/2.51      ( r2_hidden(sK1(X0,sK8),X0) != iProver_top
% 15.31/2.51      | v1_xboole_0(X0) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_7495]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7498,plain,
% 15.31/2.51      ( r2_hidden(sK1(k1_xboole_0,sK8),k1_xboole_0) != iProver_top
% 15.31/2.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_7496]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_18827,plain,
% 15.31/2.51      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)) = sK8 ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_17616,c_202,c_6700,c_7498]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_18828,plain,
% 15.31/2.51      ( k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)) = sK8
% 15.31/2.51      | u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_18827]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_18848,plain,
% 15.31/2.51      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(sK8)) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_18828,c_6473]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7489,plain,
% 15.31/2.51      ( r1_tarski(sK8,sK8) | r2_hidden(sK1(sK8,sK8),sK8) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_6692]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7491,plain,
% 15.31/2.51      ( r1_tarski(sK8,sK8) = iProver_top
% 15.31/2.51      | r2_hidden(sK1(sK8,sK8),sK8) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_7489]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_2,plain,
% 15.31/2.51      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 15.31/2.51      inference(cnf_transformation,[],[f106]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6691,plain,
% 15.31/2.51      ( r1_tarski(X0,sK8) | ~ r2_hidden(sK1(X0,sK8),sK8) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_2]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7490,plain,
% 15.31/2.51      ( r1_tarski(sK8,sK8) | ~ r2_hidden(sK1(sK8,sK8),sK8) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_6691]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7493,plain,
% 15.31/2.51      ( r1_tarski(sK8,sK8) = iProver_top
% 15.31/2.51      | r2_hidden(sK1(sK8,sK8),sK8) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_7490]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7467,plain,
% 15.31/2.51      ( m1_subset_1(X0,k1_zfmisc_1(sK8)) | ~ r1_tarski(X0,sK8) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_13]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_18648,plain,
% 15.31/2.51      ( m1_subset_1(sK8,k1_zfmisc_1(sK8)) | ~ r1_tarski(sK8,sK8) ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_7467]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_18651,plain,
% 15.31/2.51      ( m1_subset_1(sK8,k1_zfmisc_1(sK8)) = iProver_top
% 15.31/2.51      | r1_tarski(sK8,sK8) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_18648]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_19151,plain,
% 15.31/2.51      ( m1_subset_1(sK8,k1_zfmisc_1(sK8)) = iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_18848,c_7491,c_7493,c_18651]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_27900,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,sK5,sK6) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top
% 15.31/2.51      | r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK5),k1_xboole_0)) != iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_27834,c_8912]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_27910,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,sK5,sK6) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top
% 15.31/2.51      | r1_tarski(sK8,k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_27900,c_9]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_22,plain,
% 15.31/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.31/2.51      | ~ v1_xboole_0(X2)
% 15.31/2.51      | v1_xboole_0(X0) ),
% 15.31/2.51      inference(cnf_transformation,[],[f124]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6453,plain,
% 15.31/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.31/2.51      | v1_xboole_0(X2) != iProver_top
% 15.31/2.51      | v1_xboole_0(X0) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_11970,plain,
% 15.31/2.51      ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v1_xboole_0(sK8) = iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6422,c_6453]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_27890,plain,
% 15.31/2.51      ( v1_xboole_0(sK8) = iProver_top
% 15.31/2.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_27834,c_11970]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_29100,plain,
% 15.31/2.51      ( v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,sK5,sK6) != iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_27875,c_202,c_6883,c_7491,c_7493,c_15032,c_27910,c_27890]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_29101,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,sK5,sK6) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_29100]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_29104,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,sK5,sK6) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(light_normalisation,[status(thm)],[c_29101,c_28398,c_28902]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_29105,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,sK5,sK6) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_29104,c_28902]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_29107,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,sK5,sK6) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_11030,c_29105]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_6428,plain,
% 15.31/2.51      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 15.31/2.51      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 15.31/2.51      | v2_pre_topc(X1) != iProver_top
% 15.31/2.51      | v2_pre_topc(X2) != iProver_top
% 15.31/2.51      | l1_pre_topc(X1) != iProver_top
% 15.31/2.51      | l1_pre_topc(X2) != iProver_top
% 15.31/2.51      | v1_funct_1(X0) != iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_9192,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
% 15.31/2.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK5) != iProver_top
% 15.31/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK5) != iProver_top
% 15.31/2.51      | v1_funct_1(sK8) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6422,c_6428]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_9489,plain,
% 15.31/2.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_9192,c_66,c_67,c_68,c_69,c_73,c_74,c_6472,c_6474,c_6473,
% 15.31/2.51                 c_6605,c_6623,c_6669,c_6747,c_8426]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_9490,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_9489]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_9493,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6461,c_9490]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_27896,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top
% 15.31/2.51      | r1_tarski(sK8,k2_zfmisc_1(u1_struct_0(sK5),k1_xboole_0)) != iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_27834,c_9493]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_27913,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top
% 15.31/2.51      | r1_tarski(sK8,k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_27896,c_9]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_29538,plain,
% 15.31/2.51      ( v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_27913,c_202,c_6883,c_7491,c_7493,c_15032,c_27890]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_29539,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(sK5),k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_29538]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_29542,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(light_normalisation,[status(thm)],[c_29539,c_28398,c_28902]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_29543,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_29542,c_28902]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_13264,plain,
% 15.31/2.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) = iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(sK8),X0) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6422,c_6451]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_13466,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,X0,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(sK8),u1_struct_0(X0)) != iProver_top
% 15.31/2.51      | v2_pre_topc(X0) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK6) != iProver_top
% 15.31/2.51      | l1_pre_topc(X0) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK6) != iProver_top
% 15.31/2.51      | v1_funct_1(sK8) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_13264,c_6426]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_17091,plain,
% 15.31/2.51      ( v2_pre_topc(X0) != iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(sK8),u1_struct_0(X0)) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,X0,sK6) = iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_13466,c_68,c_69,c_73]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_17092,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,X0,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(sK8),u1_struct_0(X0)) != iProver_top
% 15.31/2.51      | v2_pre_topc(X0) != iProver_top
% 15.31/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_17091]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_27872,plain,
% 15.31/2.51      ( v5_pre_topc(sK8,X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(sK8,X0,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(sK8,u1_struct_0(X0),k1_xboole_0) != iProver_top
% 15.31/2.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(sK8),u1_struct_0(X0)) != iProver_top
% 15.31/2.51      | v2_pre_topc(X0) != iProver_top
% 15.31/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_27834,c_17092]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_35782,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(k1_xboole_0,X0,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) != iProver_top
% 15.31/2.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | r1_tarski(k1_relat_1(k1_xboole_0),u1_struct_0(X0)) != iProver_top
% 15.31/2.51      | v2_pre_topc(X0) != iProver_top
% 15.31/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.31/2.51      inference(light_normalisation,[status(thm)],[c_27872,c_28902]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_184,plain,
% 15.31/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.31/2.51      | r1_tarski(X0,X1) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_186,plain,
% 15.31/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.31/2.51      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_184]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_190,plain,
% 15.31/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.31/2.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_192,plain,
% 15.31/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.31/2.51      inference(instantiation,[status(thm)],[c_190]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_7918,plain,
% 15.31/2.51      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 15.31/2.51      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.31/2.51      | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))) != iProver_top
% 15.31/2.51      | v2_pre_topc(X1) != iProver_top
% 15.31/2.51      | v2_pre_topc(X2) != iProver_top
% 15.31/2.51      | l1_pre_topc(X1) != iProver_top
% 15.31/2.51      | l1_pre_topc(X2) != iProver_top
% 15.31/2.51      | v1_funct_1(X0) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6461,c_6426]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_28080,plain,
% 15.31/2.51      ( v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(X0,X1,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)) != iProver_top
% 15.31/2.51      | v2_pre_topc(X1) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK6) != iProver_top
% 15.31/2.51      | l1_pre_topc(X1) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK6) != iProver_top
% 15.31/2.51      | v1_funct_1(X0) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_27834,c_7918]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_28087,plain,
% 15.31/2.51      ( v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(X0,X1,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)) != iProver_top
% 15.31/2.51      | v2_pre_topc(X1) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK6) != iProver_top
% 15.31/2.51      | l1_pre_topc(X1) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK6) != iProver_top
% 15.31/2.51      | v1_funct_1(X0) != iProver_top ),
% 15.31/2.51      inference(light_normalisation,[status(thm)],[c_28080,c_27834]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_28088,plain,
% 15.31/2.51      ( v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(X0,X1,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 15.31/2.51      | v2_pre_topc(X1) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK6) != iProver_top
% 15.31/2.51      | l1_pre_topc(X1) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK6) != iProver_top
% 15.31/2.51      | v1_funct_1(X0) != iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_28087,c_9]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_31993,plain,
% 15.31/2.51      ( l1_pre_topc(X1) != iProver_top
% 15.31/2.51      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(X0,X1,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 15.31/2.51      | v2_pre_topc(X1) != iProver_top
% 15.31/2.51      | v1_funct_1(X0) != iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_28088,c_68,c_69]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_31994,plain,
% 15.31/2.51      ( v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(X0,X1,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 15.31/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6)))) != iProver_top
% 15.31/2.51      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 15.31/2.51      | v2_pre_topc(X1) != iProver_top
% 15.31/2.51      | l1_pre_topc(X1) != iProver_top
% 15.31/2.51      | v1_funct_1(X0) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_31993]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_31999,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(k1_xboole_0,X0,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) != iProver_top
% 15.31/2.51      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 15.31/2.51      | v2_pre_topc(X0) != iProver_top
% 15.31/2.51      | l1_pre_topc(X0) != iProver_top
% 15.31/2.51      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_6462,c_31994]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_35786,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.31/2.51      | v5_pre_topc(k1_xboole_0,X0,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) != iProver_top
% 15.31/2.51      | v2_pre_topc(X0) != iProver_top
% 15.31/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_35782,c_171,c_186,c_192,c_202,c_31999]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_35793,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,sK5,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,u1_struct_0(sK5),k1_xboole_0) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK5) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK5) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_29543,c_35786]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_35802,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,sK5,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(sK8),k1_xboole_0) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK5) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK5) != iProver_top ),
% 15.31/2.51      inference(light_normalisation,[status(thm)],[c_35793,c_28398]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_35803,plain,
% 15.31/2.51      ( v5_pre_topc(k1_xboole_0,sK5,sK6) = iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 15.31/2.51      | v2_pre_topc(sK5) != iProver_top
% 15.31/2.51      | l1_pre_topc(sK5) != iProver_top ),
% 15.31/2.51      inference(demodulation,[status(thm)],[c_35802,c_28902]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_39098,plain,
% 15.31/2.51      ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK6)) != iProver_top ),
% 15.31/2.51      inference(global_propositional_subsumption,
% 15.31/2.51                [status(thm)],
% 15.31/2.51                [c_39089,c_66,c_67,c_29107,c_35803]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_39099,plain,
% 15.31/2.51      ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 15.31/2.51      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(renaming,[status(thm)],[c_39098]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_47043,plain,
% 15.31/2.51      ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_46859,c_39099]) ).
% 15.31/2.51  
% 15.31/2.51  cnf(c_47500,plain,
% 15.31/2.51      ( $false ),
% 15.31/2.51      inference(superposition,[status(thm)],[c_11030,c_47043]) ).
% 15.31/2.51  
% 15.31/2.51  
% 15.31/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.31/2.51  
% 15.31/2.51  ------                               Statistics
% 15.31/2.51  
% 15.31/2.51  ------ General
% 15.31/2.51  
% 15.31/2.51  abstr_ref_over_cycles:                  0
% 15.31/2.51  abstr_ref_under_cycles:                 0
% 15.31/2.51  gc_basic_clause_elim:                   0
% 15.31/2.51  forced_gc_time:                         0
% 15.31/2.51  parsing_time:                           0.017
% 15.31/2.51  unif_index_cands_time:                  0.
% 15.31/2.51  unif_index_add_time:                    0.
% 15.31/2.51  orderings_time:                         0.
% 15.31/2.51  out_proof_time:                         0.035
% 15.31/2.51  total_time:                             1.534
% 15.31/2.51  num_of_symbols:                         65
% 15.31/2.51  num_of_terms:                           32037
% 15.31/2.51  
% 15.31/2.51  ------ Preprocessing
% 15.31/2.51  
% 15.31/2.51  num_of_splits:                          0
% 15.31/2.51  num_of_split_atoms:                     0
% 15.31/2.51  num_of_reused_defs:                     0
% 15.31/2.51  num_eq_ax_congr_red:                    86
% 15.31/2.51  num_of_sem_filtered_clauses:            1
% 15.31/2.51  num_of_subtypes:                        0
% 15.31/2.51  monotx_restored_types:                  0
% 15.31/2.51  sat_num_of_epr_types:                   0
% 15.31/2.51  sat_num_of_non_cyclic_types:            0
% 15.31/2.51  sat_guarded_non_collapsed_types:        0
% 15.31/2.51  num_pure_diseq_elim:                    0
% 15.31/2.51  simp_replaced_by:                       0
% 15.31/2.51  res_preprocessed:                       299
% 15.31/2.51  prep_upred:                             0
% 15.31/2.51  prep_unflattend:                        111
% 15.31/2.51  smt_new_axioms:                         0
% 15.31/2.51  pred_elim_cands:                        13
% 15.31/2.51  pred_elim:                              0
% 15.31/2.51  pred_elim_cl:                           0
% 15.31/2.51  pred_elim_cycles:                       10
% 15.31/2.51  merged_defs:                            16
% 15.31/2.51  merged_defs_ncl:                        0
% 15.31/2.51  bin_hyper_res:                          17
% 15.31/2.51  prep_cycles:                            4
% 15.31/2.51  pred_elim_time:                         0.069
% 15.31/2.51  splitting_time:                         0.
% 15.31/2.51  sem_filter_time:                        0.
% 15.31/2.51  monotx_time:                            0.001
% 15.31/2.51  subtype_inf_time:                       0.
% 15.31/2.51  
% 15.31/2.51  ------ Problem properties
% 15.31/2.51  
% 15.31/2.51  clauses:                                64
% 15.31/2.51  conjectures:                            13
% 15.31/2.51  epr:                                    14
% 15.31/2.51  horn:                                   56
% 15.31/2.51  ground:                                 14
% 15.31/2.51  unary:                                  21
% 15.31/2.51  binary:                                 18
% 15.31/2.51  lits:                                   189
% 15.31/2.51  lits_eq:                                17
% 15.31/2.51  fd_pure:                                0
% 15.31/2.51  fd_pseudo:                              0
% 15.31/2.51  fd_cond:                                5
% 15.31/2.51  fd_pseudo_cond:                         2
% 15.31/2.51  ac_symbols:                             0
% 15.31/2.51  
% 15.31/2.51  ------ Propositional Solver
% 15.31/2.51  
% 15.31/2.51  prop_solver_calls:                      37
% 15.31/2.51  prop_fast_solver_calls:                 8522
% 15.31/2.51  smt_solver_calls:                       0
% 15.31/2.51  smt_fast_solver_calls:                  0
% 15.31/2.51  prop_num_of_clauses:                    18177
% 15.31/2.51  prop_preprocess_simplified:             35849
% 15.31/2.51  prop_fo_subsumed:                       825
% 15.31/2.51  prop_solver_time:                       0.
% 15.31/2.51  smt_solver_time:                        0.
% 15.31/2.51  smt_fast_solver_time:                   0.
% 15.31/2.51  prop_fast_solver_time:                  0.
% 15.31/2.51  prop_unsat_core_time:                   0.
% 15.31/2.51  
% 15.31/2.51  ------ QBF
% 15.31/2.51  
% 15.31/2.51  qbf_q_res:                              0
% 15.31/2.51  qbf_num_tautologies:                    0
% 15.31/2.51  qbf_prep_cycles:                        0
% 15.31/2.51  
% 15.31/2.51  ------ BMC1
% 15.31/2.51  
% 15.31/2.51  bmc1_current_bound:                     -1
% 15.31/2.51  bmc1_last_solved_bound:                 -1
% 15.31/2.51  bmc1_unsat_core_size:                   -1
% 15.31/2.51  bmc1_unsat_core_parents_size:           -1
% 15.31/2.51  bmc1_merge_next_fun:                    0
% 15.31/2.51  bmc1_unsat_core_clauses_time:           0.
% 15.31/2.51  
% 15.31/2.51  ------ Instantiation
% 15.31/2.51  
% 15.31/2.51  inst_num_of_clauses:                    4330
% 15.31/2.51  inst_num_in_passive:                    2410
% 15.31/2.51  inst_num_in_active:                     1782
% 15.31/2.51  inst_num_in_unprocessed:                140
% 15.31/2.51  inst_num_of_loops:                      2630
% 15.31/2.51  inst_num_of_learning_restarts:          0
% 15.31/2.51  inst_num_moves_active_passive:          841
% 15.31/2.51  inst_lit_activity:                      0
% 15.31/2.51  inst_lit_activity_moves:                0
% 15.31/2.51  inst_num_tautologies:                   0
% 15.31/2.51  inst_num_prop_implied:                  0
% 15.31/2.51  inst_num_existing_simplified:           0
% 15.31/2.51  inst_num_eq_res_simplified:             0
% 15.31/2.51  inst_num_child_elim:                    0
% 15.31/2.51  inst_num_of_dismatching_blockings:      2471
% 15.31/2.51  inst_num_of_non_proper_insts:           6113
% 15.31/2.51  inst_num_of_duplicates:                 0
% 15.31/2.51  inst_inst_num_from_inst_to_res:         0
% 15.31/2.51  inst_dismatching_checking_time:         0.
% 15.31/2.51  
% 15.31/2.51  ------ Resolution
% 15.31/2.51  
% 15.31/2.51  res_num_of_clauses:                     0
% 15.31/2.51  res_num_in_passive:                     0
% 15.31/2.51  res_num_in_active:                      0
% 15.31/2.51  res_num_of_loops:                       303
% 15.31/2.51  res_forward_subset_subsumed:            264
% 15.31/2.51  res_backward_subset_subsumed:           4
% 15.31/2.51  res_forward_subsumed:                   0
% 15.31/2.51  res_backward_subsumed:                  1
% 15.31/2.51  res_forward_subsumption_resolution:     5
% 15.31/2.51  res_backward_subsumption_resolution:    0
% 15.31/2.51  res_clause_to_clause_subsumption:       4198
% 15.31/2.51  res_orphan_elimination:                 0
% 15.31/2.51  res_tautology_del:                      503
% 15.31/2.51  res_num_eq_res_simplified:              0
% 15.31/2.51  res_num_sel_changes:                    0
% 15.31/2.51  res_moves_from_active_to_pass:          0
% 15.31/2.51  
% 15.31/2.51  ------ Superposition
% 15.31/2.51  
% 15.31/2.51  sup_time_total:                         0.
% 15.31/2.51  sup_time_generating:                    0.
% 15.31/2.51  sup_time_sim_full:                      0.
% 15.31/2.51  sup_time_sim_immed:                     0.
% 15.31/2.51  
% 15.31/2.51  sup_num_of_clauses:                     1017
% 15.31/2.51  sup_num_in_active:                      270
% 15.31/2.51  sup_num_in_passive:                     747
% 15.31/2.51  sup_num_of_loops:                       525
% 15.31/2.51  sup_fw_superposition:                   1253
% 15.31/2.51  sup_bw_superposition:                   1255
% 15.31/2.51  sup_immediate_simplified:               894
% 15.31/2.51  sup_given_eliminated:                   19
% 15.31/2.51  comparisons_done:                       0
% 15.31/2.51  comparisons_avoided:                    33
% 15.31/2.51  
% 15.31/2.51  ------ Simplifications
% 15.31/2.51  
% 15.31/2.51  
% 15.31/2.51  sim_fw_subset_subsumed:                 192
% 15.31/2.51  sim_bw_subset_subsumed:                 414
% 15.31/2.51  sim_fw_subsumed:                        169
% 15.31/2.51  sim_bw_subsumed:                        103
% 15.31/2.52  sim_fw_subsumption_res:                 0
% 15.31/2.52  sim_bw_subsumption_res:                 0
% 15.31/2.52  sim_tautology_del:                      122
% 15.31/2.52  sim_eq_tautology_del:                   56
% 15.31/2.52  sim_eq_res_simp:                        0
% 15.31/2.52  sim_fw_demodulated:                     357
% 15.31/2.52  sim_bw_demodulated:                     162
% 15.31/2.52  sim_light_normalised:                   643
% 15.31/2.52  sim_joinable_taut:                      0
% 15.31/2.52  sim_joinable_simp:                      0
% 15.31/2.52  sim_ac_normalised:                      0
% 15.31/2.52  sim_smt_subsumption:                    0
% 15.31/2.52  
%------------------------------------------------------------------------------
