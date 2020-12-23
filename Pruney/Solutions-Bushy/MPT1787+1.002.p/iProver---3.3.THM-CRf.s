%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1787+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:24 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 360 expanded)
%              Number of clauses        :   69 ( 107 expanded)
%              Number of leaves         :   19 (  88 expanded)
%              Depth                    :   23
%              Number of atoms          :  534 (1486 expanded)
%              Number of equality atoms :  125 ( 144 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r2_hidden(X1,k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r2_hidden(X1,k5_tmap_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(sK8,k5_tmap_1(X0,sK8))
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(X1,k5_tmap_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(X1,k5_tmap_1(sK7,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) )
      & l1_pre_topc(sK7)
      & v2_pre_topc(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ~ r2_hidden(sK8,k5_tmap_1(sK7,sK8))
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f39,f60,f59])).

fof(f98,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f61])).

fof(f97,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f61])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f99,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f61])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f96,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f61])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,u1_pre_topc(X1))
          & r2_hidden(X5,u1_pre_topc(X1))
          & k4_subset_1(u1_struct_0(X1),X5,k9_subset_1(u1_struct_0(X1),X6,X2)) = X0
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(sK6(X0,X1,X2),u1_pre_topc(X1))
        & r2_hidden(sK5(X0,X1,X2),u1_pre_topc(X1))
        & k4_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),X2)) = X0
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),u1_pre_topc(X1))
            & r2_hidden(sK5(X0,X1,X2),u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),X2)) = X0
            & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f55,f56])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f101,plain,(
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
    inference(equality_resolution,[],[f86])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f41,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f23,f40])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
            & r1_tarski(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f100,plain,(
    ~ r2_hidden(sK8,k5_tmap_1(sK7,sK8)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_33,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_668,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_36])).

cnf(c_669,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK7))
    | ~ v2_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_45,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK7))
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_671,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_669,c_37,c_36,c_45])).

cnf(c_1839,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_17,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_679,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_36])).

cnf(c_680,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_1838,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1849,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3822,plain,
    ( r2_hidden(X0,u1_pre_topc(sK7)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_1849])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1847,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1851,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5169,plain,
    ( k4_subset_1(u1_struct_0(sK7),X0,sK8) = k2_xboole_0(X0,sK8)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1847,c_1851])).

cnf(c_5504,plain,
    ( k4_subset_1(u1_struct_0(sK7),X0,sK8) = k2_xboole_0(X0,sK8)
    | r2_hidden(X0,u1_pre_topc(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3822,c_5169])).

cnf(c_5576,plain,
    ( k4_subset_1(u1_struct_0(sK7),k1_xboole_0,sK8) = k2_xboole_0(k1_xboole_0,sK8) ),
    inference(superposition,[status(thm)],[c_1839,c_5504])).

cnf(c_27,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2401,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_27,c_0])).

cnf(c_5590,plain,
    ( k4_subset_1(u1_struct_0(sK7),k1_xboole_0,sK8) = sK8 ),
    inference(demodulation,[status(thm)],[c_5576,c_2401])).

cnf(c_31,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_284,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_28,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_787,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_284,c_28])).

cnf(c_1834,plain,
    ( k3_xboole_0(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_2861,plain,
    ( k3_xboole_0(sK8,u1_struct_0(sK7)) = sK8 ),
    inference(superposition,[status(thm)],[c_1847,c_1834])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | a_2_0_tmap_1(X1,X0) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | a_2_0_tmap_1(X1,X0) = k5_tmap_1(X1,X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_38])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | a_2_0_tmap_1(sK7,X0) = k5_tmap_1(sK7,X0) ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_625,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | a_2_0_tmap_1(sK7,X0) = k5_tmap_1(sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_621,c_37,c_36])).

cnf(c_1840,plain,
    ( a_2_0_tmap_1(sK7,X0) = k5_tmap_1(sK7,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_2236,plain,
    ( a_2_0_tmap_1(sK7,sK8) = k5_tmap_1(sK7,sK8) ),
    inference(superposition,[status(thm)],[c_1847,c_1840])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k4_subset_1(u1_struct_0(X1),X2,k9_subset_1(u1_struct_0(X1),X0,X3)),a_2_0_tmap_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_590,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k4_subset_1(u1_struct_0(X1),X2,k9_subset_1(u1_struct_0(X1),X0,X3)),a_2_0_tmap_1(X1,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_38])).

cnf(c_591,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK7))
    | ~ r2_hidden(X1,u1_pre_topc(sK7))
    | r2_hidden(k4_subset_1(u1_struct_0(sK7),X0,k9_subset_1(u1_struct_0(sK7),X1,X2)),a_2_0_tmap_1(sK7,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_595,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK7))
    | ~ r2_hidden(X1,u1_pre_topc(sK7))
    | r2_hidden(k4_subset_1(u1_struct_0(sK7),X0,k9_subset_1(u1_struct_0(sK7),X1,X2)),a_2_0_tmap_1(sK7,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_37,c_36])).

cnf(c_596,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK7))
    | ~ r2_hidden(X1,u1_pre_topc(sK7))
    | r2_hidden(k4_subset_1(u1_struct_0(sK7),X0,k9_subset_1(u1_struct_0(sK7),X1,X2)),a_2_0_tmap_1(sK7,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(renaming,[status(thm)],[c_595])).

cnf(c_1841,plain,
    ( r2_hidden(X0,u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK7),X0,k9_subset_1(u1_struct_0(sK7),X1,X2)),a_2_0_tmap_1(sK7,X2)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_2707,plain,
    ( r2_hidden(X0,u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK7),X0,k9_subset_1(u1_struct_0(sK7),X1,sK8)),k5_tmap_1(sK7,sK8)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2236,c_1841])).

cnf(c_42,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7228,plain,
    ( r2_hidden(X0,u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK7),X0,k9_subset_1(u1_struct_0(sK7),X1,sK8)),k5_tmap_1(sK7,sK8)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2707,c_42,c_3822])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1850,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4249,plain,
    ( k9_subset_1(u1_struct_0(sK7),X0,sK8) = k3_xboole_0(X0,sK8) ),
    inference(superposition,[status(thm)],[c_1847,c_1850])).

cnf(c_7234,plain,
    ( r2_hidden(X0,u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK7),X0,k3_xboole_0(X1,sK8)),k5_tmap_1(sK7,sK8)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7228,c_4249])).

cnf(c_7239,plain,
    ( r2_hidden(X0,u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK7),X0,k3_xboole_0(X1,sK8)),k5_tmap_1(sK7,sK8)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7234,c_3822])).

cnf(c_7243,plain,
    ( r2_hidden(X0,u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK7),X0,k3_xboole_0(sK8,X1)),k5_tmap_1(sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_7239])).

cnf(c_7851,plain,
    ( r2_hidden(X0,u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK7),X0,sK8),k5_tmap_1(sK7,sK8)) = iProver_top
    | r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2861,c_7243])).

cnf(c_40,plain,
    ( v2_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_41,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_14,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_97,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_99,plain,
    ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) = iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_7993,plain,
    ( r2_hidden(k4_subset_1(u1_struct_0(sK7),X0,sK8),k5_tmap_1(sK7,sK8)) = iProver_top
    | r2_hidden(X0,u1_pre_topc(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7851,c_40,c_41,c_99])).

cnf(c_7994,plain,
    ( r2_hidden(X0,u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK7),X0,sK8),k5_tmap_1(sK7,sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7993])).

cnf(c_11469,plain,
    ( r2_hidden(sK8,k5_tmap_1(sK7,sK8)) = iProver_top
    | r2_hidden(k1_xboole_0,u1_pre_topc(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5590,c_7994])).

cnf(c_44,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_46,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK7)) = iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_34,negated_conjecture,
    ( ~ r2_hidden(sK8,k5_tmap_1(sK7,sK8)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_43,plain,
    ( r2_hidden(sK8,k5_tmap_1(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11469,c_46,c_43,c_41,c_40])).


%------------------------------------------------------------------------------
