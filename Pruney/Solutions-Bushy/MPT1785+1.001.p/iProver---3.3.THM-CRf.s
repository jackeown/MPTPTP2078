%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1785+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:24 EST 2020

% Result     : Theorem 50.94s
% Output     : CNFRefutation 50.94s
% Verified   : 
% Statistics : Number of formulae       :  190 (2514 expanded)
%              Number of clauses        :  116 ( 741 expanded)
%              Number of leaves         :   20 ( 612 expanded)
%              Depth                    :   26
%              Number of atoms          :  712 (10865 expanded)
%              Number of equality atoms :  299 (1671 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(a_2_1_tmap_1(X0,X1),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(a_2_1_tmap_1(X0,X1),k5_tmap_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(a_2_1_tmap_1(X0,X1),k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(a_2_1_tmap_1(X0,X1),k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(a_2_1_tmap_1(X0,X1),k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(a_2_1_tmap_1(X0,sK6),k5_tmap_1(X0,sK6))
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(a_2_1_tmap_1(X0,X1),k5_tmap_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(a_2_1_tmap_1(sK5,X1),k5_tmap_1(sK5,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ~ r1_tarski(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f38,f52,f51])).

fof(f81,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f53])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,u1_pre_topc(X1))
            & k9_subset_1(u1_struct_0(X1),X3,X2) = X0
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,u1_pre_topc(X1))
            & k9_subset_1(u1_struct_0(X1),X3,X2) = X0
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,u1_pre_topc(X1))
            & k9_subset_1(u1_struct_0(X1),X3,X2) = X0
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,u1_pre_topc(X1))
              | k9_subset_1(u1_struct_0(X1),X3,X2) != X0
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,u1_pre_topc(X1))
              & k9_subset_1(u1_struct_0(X1),X3,X2) = X0
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,u1_pre_topc(X1))
              | k9_subset_1(u1_struct_0(X1),X3,X2) != X0
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,u1_pre_topc(X1))
              & k9_subset_1(u1_struct_0(X1),X4,X2) = X0
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,u1_pre_topc(X1))
          & k9_subset_1(u1_struct_0(X1),X4,X2) = X0
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X1))
        & k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,u1_pre_topc(X1))
              | k9_subset_1(u1_struct_0(X1),X3,X2) != X0
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X1))
            & k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | k9_subset_1(u1_struct_0(X1),X3,X2) != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X1),X3,X2),a_2_1_tmap_1(X1,X2))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),X2) = X0
      | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f39])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    ~ r1_tarski(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X3,X4] :
              ( r2_hidden(X4,u1_pre_topc(X1))
              & r2_hidden(X3,u1_pre_topc(X1))
              & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X5,X6] :
              ( r2_hidden(X6,u1_pre_topc(X1))
              & r2_hidden(X5,u1_pre_topc(X1))
              & k4_subset_1(u1_struct_0(X1),X5,k9_subset_1(u1_struct_0(X1),X6,X2)) = X0
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,u1_pre_topc(X1))
          & r2_hidden(X5,u1_pre_topc(X1))
          & k4_subset_1(u1_struct_0(X1),X5,k9_subset_1(u1_struct_0(X1),X6,X2)) = X0
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(sK3(X0,X1,X2),u1_pre_topc(X1))
        & r2_hidden(sK2(X0,X1,X2),u1_pre_topc(X1))
        & k4_subset_1(u1_struct_0(X1),sK2(X0,X1,X2),k9_subset_1(u1_struct_0(X1),sK3(X0,X1,X2),X2)) = X0
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),u1_pre_topc(X1))
            & r2_hidden(sK2(X0,X1,X2),u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),sK2(X0,X1,X2),k9_subset_1(u1_struct_0(X1),sK3(X0,X1,X2),X2)) = X0
            & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f45])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      | ~ r2_hidden(X4,u1_pre_topc(X1))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)),a_2_0_tmap_1(X1,X2))
      | ~ r2_hidden(X4,u1_pre_topc(X1))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X1))
      | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_21,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1265,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_21,c_0])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_707,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_711,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1745,plain,
    ( k9_subset_1(u1_struct_0(sK5),X0,sK6) = k3_xboole_0(X0,sK6) ),
    inference(superposition,[status(thm)],[c_707,c_711])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X0,X2),a_2_1_tmap_1(X1,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_716,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X0,X2),a_2_1_tmap_1(X1,X2)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_6,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2180,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_22,c_6])).

cnf(c_3482,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X0,X2),a_2_1_tmap_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2180,c_14])).

cnf(c_3484,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X0,X2),a_2_1_tmap_1(X1,X2)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3482])).

cnf(c_7166,plain,
    ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X0,X2),a_2_1_tmap_1(X1,X2)) = iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_716,c_3484])).

cnf(c_7167,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X0,X2),a_2_1_tmap_1(X1,X2)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7166])).

cnf(c_7177,plain,
    ( r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k3_xboole_0(X0,sK6),a_2_1_tmap_1(sK5,sK6)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_7167])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_29,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8192,plain,
    ( r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k3_xboole_0(X0,sK6),a_2_1_tmap_1(sK5,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7177,c_29,c_30,c_31,c_32])).

cnf(c_8202,plain,
    ( r2_hidden(k1_xboole_0,a_2_1_tmap_1(sK5,sK6)) = iProver_top
    | r2_hidden(k1_xboole_0,u1_pre_topc(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1265,c_8192])).

cnf(c_23,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_34,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X0)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_36,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK5)) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_11412,plain,
    ( r2_hidden(k1_xboole_0,a_2_1_tmap_1(sK5,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8202,c_30,c_31,c_36])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),X2) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_714,plain,
    ( k9_subset_1(u1_struct_0(X0),sK4(X1,X0,X2),X2) = X1
    | r2_hidden(X1,a_2_1_tmap_1(X0,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11417,plain,
    ( k9_subset_1(u1_struct_0(sK5),sK4(k1_xboole_0,sK5,sK6),sK6) = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_11412,c_714])).

cnf(c_11433,plain,
    ( k3_xboole_0(sK4(k1_xboole_0,sK5,sK6),sK6) = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11417,c_1745])).

cnf(c_709,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X0)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8203,plain,
    ( k9_subset_1(u1_struct_0(sK5),sK4(k3_xboole_0(X0,sK6),sK5,sK6),sK6) = k3_xboole_0(X0,sK6)
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_8192,c_714])).

cnf(c_8224,plain,
    ( k3_xboole_0(sK4(k3_xboole_0(X0,sK6),sK5,sK6),sK6) = k3_xboole_0(X0,sK6)
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8203,c_1745])).

cnf(c_8532,plain,
    ( k3_xboole_0(sK4(k3_xboole_0(X0,sK6),sK5,sK6),sK6) = k3_xboole_0(X0,sK6)
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8224,c_29,c_30,c_31,c_32])).

cnf(c_8544,plain,
    ( k3_xboole_0(sK4(k3_xboole_0(k1_xboole_0,sK6),sK5,sK6),sK6) = k3_xboole_0(k1_xboole_0,sK6)
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_8532])).

cnf(c_8548,plain,
    ( k3_xboole_0(sK4(k1_xboole_0,sK5,sK6),sK6) = k1_xboole_0
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8544,c_1265])).

cnf(c_11443,plain,
    ( k3_xboole_0(sK4(k1_xboole_0,sK5,sK6),sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11433,c_30,c_31,c_8548])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_727,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5212,plain,
    ( k9_subset_1(u1_struct_0(X0),sK4(sK0(a_2_1_tmap_1(X0,X1),X2),X0,X1),X1) = sK0(a_2_1_tmap_1(X0,X1),X2)
    | r1_tarski(a_2_1_tmap_1(X0,X1),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_727,c_714])).

cnf(c_90516,plain,
    ( k9_subset_1(u1_struct_0(sK5),sK4(sK0(a_2_1_tmap_1(sK5,sK6),X0),sK5,sK6),sK6) = sK0(a_2_1_tmap_1(sK5,sK6),X0)
    | r1_tarski(a_2_1_tmap_1(sK5,sK6),X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_707,c_5212])).

cnf(c_90605,plain,
    ( k3_xboole_0(sK4(sK0(a_2_1_tmap_1(sK5,sK6),X0),sK5,sK6),sK6) = sK0(a_2_1_tmap_1(sK5,sK6),X0)
    | r1_tarski(a_2_1_tmap_1(sK5,sK6),X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_90516,c_1745])).

cnf(c_91093,plain,
    ( r1_tarski(a_2_1_tmap_1(sK5,sK6),X0) = iProver_top
    | k3_xboole_0(sK4(sK0(a_2_1_tmap_1(sK5,sK6),X0),sK5,sK6),sK6) = sK0(a_2_1_tmap_1(sK5,sK6),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_90605,c_29,c_30,c_31])).

cnf(c_91094,plain,
    ( k3_xboole_0(sK4(sK0(a_2_1_tmap_1(sK5,sK6),X0),sK5,sK6),sK6) = sK0(a_2_1_tmap_1(sK5,sK6),X0)
    | r1_tarski(a_2_1_tmap_1(sK5,sK6),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_91093])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_708,plain,
    ( r1_tarski(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_91101,plain,
    ( k3_xboole_0(sK4(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),sK5,sK6),sK6) = sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)) ),
    inference(superposition,[status(thm)],[c_91094,c_708])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_725,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2122,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_725])).

cnf(c_2146,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2122,c_32])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_712,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2691,plain,
    ( k4_subset_1(u1_struct_0(sK5),X0,k3_xboole_0(X1,sK6)) = k2_xboole_0(X0,k3_xboole_0(X1,sK6))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2146,c_712])).

cnf(c_16830,plain,
    ( k4_subset_1(u1_struct_0(sK5),k3_xboole_0(X0,sK6),k3_xboole_0(X1,sK6)) = k2_xboole_0(k3_xboole_0(X0,sK6),k3_xboole_0(X1,sK6)) ),
    inference(superposition,[status(thm)],[c_2146,c_2691])).

cnf(c_19500,plain,
    ( k4_subset_1(u1_struct_0(sK5),k3_xboole_0(sK6,X0),k3_xboole_0(X1,sK6)) = k2_xboole_0(k3_xboole_0(X0,sK6),k3_xboole_0(X1,sK6)) ),
    inference(superposition,[status(thm)],[c_0,c_16830])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | a_2_0_tmap_1(X1,X0) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_726,plain,
    ( a_2_0_tmap_1(X0,X1) = k5_tmap_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4408,plain,
    ( a_2_0_tmap_1(sK5,sK6) = k5_tmap_1(sK5,sK6)
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_707,c_726])).

cnf(c_1107,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | a_2_0_tmap_1(sK5,sK6) = k5_tmap_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4710,plain,
    ( a_2_0_tmap_1(sK5,sK6) = k5_tmap_1(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4408,c_28,c_27,c_26,c_25,c_1107])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k4_subset_1(u1_struct_0(X1),X2,k9_subset_1(u1_struct_0(X1),X0,X3)),a_2_0_tmap_1(X1,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_722,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(X2,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(X1),X2,k9_subset_1(u1_struct_0(X1),X0,X3)),a_2_0_tmap_1(X1,X3)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3481,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k4_subset_1(u1_struct_0(X1),X2,k9_subset_1(u1_struct_0(X1),X0,X3)),a_2_0_tmap_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2180,c_8])).

cnf(c_3485,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(X2,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(X1),X2,k9_subset_1(u1_struct_0(X1),X0,X3)),a_2_0_tmap_1(X1,X3)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3481])).

cnf(c_10163,plain,
    ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(X1),X2,k9_subset_1(u1_struct_0(X1),X0,X3)),a_2_0_tmap_1(X1,X3)) = iProver_top
    | r2_hidden(X2,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_722,c_3485])).

cnf(c_10164,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(X2,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(X1),X2,k9_subset_1(u1_struct_0(X1),X0,X3)),a_2_0_tmap_1(X1,X3)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_10163])).

cnf(c_10180,plain,
    ( r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK5),X0,k9_subset_1(u1_struct_0(sK5),X1,sK6)),k5_tmap_1(sK5,sK6)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4710,c_10164])).

cnf(c_10274,plain,
    ( r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK5),X0,k3_xboole_0(X1,sK6)),k5_tmap_1(sK5,sK6)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10180,c_1745])).

cnf(c_11118,plain,
    ( r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK5),X0,k3_xboole_0(X1,sK6)),k5_tmap_1(sK5,sK6)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10274,c_29,c_30,c_31,c_32])).

cnf(c_22465,plain,
    ( r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k2_xboole_0(k3_xboole_0(X1,sK6),k3_xboole_0(X0,sK6)),k5_tmap_1(sK5,sK6)) = iProver_top
    | r2_hidden(k3_xboole_0(sK6,X1),u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(k3_xboole_0(sK6,X1),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19500,c_11118])).

cnf(c_2153,plain,
    ( m1_subset_1(k3_xboole_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2146])).

cnf(c_75654,plain,
    ( r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k2_xboole_0(k3_xboole_0(X1,sK6),k3_xboole_0(X0,sK6)),k5_tmap_1(sK5,sK6)) = iProver_top
    | r2_hidden(k3_xboole_0(sK6,X1),u1_pre_topc(sK5)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_22465,c_2153])).

cnf(c_91310,plain,
    ( r2_hidden(sK4(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),sK5,sK6),u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k2_xboole_0(k3_xboole_0(X0,sK6),sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6))),k5_tmap_1(sK5,sK6)) = iProver_top
    | r2_hidden(k3_xboole_0(sK6,X0),u1_pre_topc(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_91101,c_75654])).

cnf(c_33,plain,
    ( r1_tarski(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1159,plain,
    ( r2_hidden(sK0(a_2_1_tmap_1(X0,X1),X2),a_2_1_tmap_1(X0,X1))
    | r1_tarski(a_2_1_tmap_1(X0,X1),X2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3781,plain,
    ( r2_hidden(sK0(a_2_1_tmap_1(sK5,sK6),X0),a_2_1_tmap_1(sK5,sK6))
    | r1_tarski(a_2_1_tmap_1(sK5,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_15631,plain,
    ( r2_hidden(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),a_2_1_tmap_1(sK5,sK6))
    | r1_tarski(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3781])).

cnf(c_15632,plain,
    ( r2_hidden(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),a_2_1_tmap_1(sK5,sK6)) = iProver_top
    | r1_tarski(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15631])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2))
    | r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1158,plain,
    ( r2_hidden(sK4(sK0(a_2_1_tmap_1(X0,X1),X2),X0,X1),u1_pre_topc(X0))
    | ~ r2_hidden(sK0(a_2_1_tmap_1(X0,X1),X2),a_2_1_tmap_1(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_9390,plain,
    ( r2_hidden(sK4(sK0(a_2_1_tmap_1(X0,sK6),X1),X0,sK6),u1_pre_topc(X0))
    | ~ r2_hidden(sK0(a_2_1_tmap_1(X0,sK6),X1),a_2_1_tmap_1(X0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_37148,plain,
    ( r2_hidden(sK4(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),sK5,sK6),u1_pre_topc(sK5))
    | ~ r2_hidden(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),a_2_1_tmap_1(sK5,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_9390])).

cnf(c_37149,plain,
    ( r2_hidden(sK4(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),sK5,sK6),u1_pre_topc(sK5)) = iProver_top
    | r2_hidden(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),a_2_1_tmap_1(sK5,sK6)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37148])).

cnf(c_131597,plain,
    ( r2_hidden(k2_xboole_0(k3_xboole_0(X0,sK6),sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6))),k5_tmap_1(sK5,sK6)) = iProver_top
    | r2_hidden(k3_xboole_0(sK6,X0),u1_pre_topc(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_91310,c_29,c_30,c_31,c_32,c_33,c_15632,c_37149])).

cnf(c_131610,plain,
    ( r2_hidden(k2_xboole_0(k1_xboole_0,sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6))),k5_tmap_1(sK5,sK6)) = iProver_top
    | r2_hidden(k3_xboole_0(sK6,sK4(k1_xboole_0,sK5,sK6)),u1_pre_topc(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11443,c_131597])).

cnf(c_11446,plain,
    ( k3_xboole_0(sK6,sK4(k1_xboole_0,sK5,sK6)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_11443])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_729,plain,
    ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4169,plain,
    ( k4_subset_1(X0,k9_subset_1(X0,X1,X2),X3) = k4_subset_1(X0,X3,k9_subset_1(X0,X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_725,c_729])).

cnf(c_51560,plain,
    ( k4_subset_1(u1_struct_0(sK5),k9_subset_1(u1_struct_0(sK5),X0,sK6),X1) = k4_subset_1(u1_struct_0(sK5),X1,k9_subset_1(u1_struct_0(sK5),X0,sK6))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_707,c_4169])).

cnf(c_51614,plain,
    ( k4_subset_1(u1_struct_0(sK5),X0,k3_xboole_0(X1,sK6)) = k4_subset_1(u1_struct_0(sK5),k3_xboole_0(X1,sK6),X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_51560,c_1745])).

cnf(c_53591,plain,
    ( k4_subset_1(u1_struct_0(sK5),k3_xboole_0(X0,sK6),k9_subset_1(u1_struct_0(sK5),X1,X2)) = k4_subset_1(u1_struct_0(sK5),k9_subset_1(u1_struct_0(sK5),X1,X2),k3_xboole_0(X0,sK6))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_725,c_51614])).

cnf(c_56216,plain,
    ( k4_subset_1(u1_struct_0(sK5),k9_subset_1(u1_struct_0(sK5),X0,sK6),k3_xboole_0(X1,sK6)) = k4_subset_1(u1_struct_0(sK5),k3_xboole_0(X1,sK6),k9_subset_1(u1_struct_0(sK5),X0,sK6)) ),
    inference(superposition,[status(thm)],[c_707,c_53591])).

cnf(c_2692,plain,
    ( k4_subset_1(u1_struct_0(sK5),X0,k3_xboole_0(sK6,X1)) = k2_xboole_0(X0,k3_xboole_0(sK6,X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2153,c_712])).

cnf(c_33432,plain,
    ( k4_subset_1(u1_struct_0(sK5),k3_xboole_0(X0,sK6),k3_xboole_0(sK6,X1)) = k2_xboole_0(k3_xboole_0(X0,sK6),k3_xboole_0(sK6,X1)) ),
    inference(superposition,[status(thm)],[c_2146,c_2692])).

cnf(c_34993,plain,
    ( k4_subset_1(u1_struct_0(sK5),k3_xboole_0(X0,sK6),k3_xboole_0(X1,sK6)) = k2_xboole_0(k3_xboole_0(X0,sK6),k3_xboole_0(sK6,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_33432])).

cnf(c_56241,plain,
    ( k4_subset_1(u1_struct_0(sK5),k3_xboole_0(X0,sK6),k3_xboole_0(X1,sK6)) = k2_xboole_0(k3_xboole_0(X1,sK6),k3_xboole_0(sK6,X0)) ),
    inference(light_normalisation,[status(thm)],[c_56216,c_1745,c_34993])).

cnf(c_91446,plain,
    ( k2_xboole_0(k3_xboole_0(sK4(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),sK5,sK6),sK6),k3_xboole_0(sK6,X0)) = k4_subset_1(u1_struct_0(sK5),k3_xboole_0(X0,sK6),sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6))) ),
    inference(superposition,[status(thm)],[c_91101,c_56241])).

cnf(c_91459,plain,
    ( k2_xboole_0(k3_xboole_0(X0,sK6),k3_xboole_0(sK4(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),sK5,sK6),sK6)) = k4_subset_1(u1_struct_0(sK5),k3_xboole_0(X0,sK6),sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6))) ),
    inference(superposition,[status(thm)],[c_91101,c_16830])).

cnf(c_91478,plain,
    ( k4_subset_1(u1_struct_0(sK5),k3_xboole_0(X0,sK6),sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6))) = k2_xboole_0(k3_xboole_0(X0,sK6),sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6))) ),
    inference(light_normalisation,[status(thm)],[c_91459,c_91101])).

cnf(c_91507,plain,
    ( k2_xboole_0(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),k3_xboole_0(sK6,X0)) = k2_xboole_0(k3_xboole_0(X0,sK6),sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6))) ),
    inference(light_normalisation,[status(thm)],[c_91446,c_91101,c_91478])).

cnf(c_103499,plain,
    ( k2_xboole_0(k3_xboole_0(sK4(k1_xboole_0,sK5,sK6),sK6),sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6))) = k2_xboole_0(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11446,c_91507])).

cnf(c_103519,plain,
    ( k2_xboole_0(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),k1_xboole_0) = k2_xboole_0(k1_xboole_0,sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6))) ),
    inference(light_normalisation,[status(thm)],[c_103499,c_11443])).

cnf(c_20,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_103520,plain,
    ( k2_xboole_0(k1_xboole_0,sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6))) = sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)) ),
    inference(demodulation,[status(thm)],[c_103519,c_20])).

cnf(c_131689,plain,
    ( r2_hidden(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),k5_tmap_1(sK5,sK6)) = iProver_top
    | r2_hidden(k1_xboole_0,u1_pre_topc(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_131610,c_11446,c_103520])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1016,plain,
    ( ~ r2_hidden(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),k5_tmap_1(sK5,sK6))
    | r1_tarski(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1017,plain,
    ( r2_hidden(sK0(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)),k5_tmap_1(sK5,sK6)) != iProver_top
    | r1_tarski(a_2_1_tmap_1(sK5,sK6),k5_tmap_1(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_131689,c_1017,c_36,c_33,c_31,c_30])).


%------------------------------------------------------------------------------
