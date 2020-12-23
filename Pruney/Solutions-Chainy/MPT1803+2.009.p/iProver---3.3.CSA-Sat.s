%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:10 EST 2020

% Result     : CounterSatisfiable 2.52s
% Output     : Saturation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  290 (4647 expanded)
%              Number of clauses        :  214 (1096 expanded)
%              Number of leaves         :   30 (1429 expanded)
%              Depth                    :   28
%              Number of atoms          : 1332 (27826 expanded)
%              Number of equality atoms :  371 (1522 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK3)
        & m1_subset_1(sK3,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r1_tmap_1(sK2,k8_tmap_1(X0,sK2),k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),X2)
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(sK1,X1),k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK3)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f46,f45,f44])).

fof(f72,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK0(X0,X1,X2)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X2,X0,X3] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f77,plain,(
    ~ r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2850,plain,
    ( k5_tmap_1(X0_57,X0_56) = k5_tmap_1(X1_57,X0_56)
    | X0_57 != X1_57 ),
    theory(equality)).

cnf(c_2849,plain,
    ( u1_pre_topc(X0_57) = u1_pre_topc(X1_57)
    | X0_57 != X1_57 ),
    theory(equality)).

cnf(c_2836,plain,
    ( X0_58 != X1_58
    | X2_58 != X1_58
    | X2_58 = X0_58 ),
    theory(equality)).

cnf(c_2832,plain,
    ( X0_58 = X0_58 ),
    theory(equality)).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1284,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_1285,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_1284])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1289,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1285,c_29,c_27])).

cnf(c_2814,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_pre_topc(k6_tmap_1(sK1,X0_56)) = k5_tmap_1(sK1,X0_56) ),
    inference(subtyping,[status(esa)],[c_1289])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_952,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_953,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_952])).

cnf(c_955,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_953,c_29,c_28,c_27])).

cnf(c_1377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(resolution_lifted,[status(thm)],[c_18,c_955])).

cnf(c_1378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0) ),
    inference(unflattening,[status(thm)],[c_1377])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_963,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_964,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_963])).

cnf(c_1382,plain,
    ( v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1378,c_29,c_28,c_27,c_964])).

cnf(c_1383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0) ),
    inference(renaming,[status(thm)],[c_1382])).

cnf(c_2809,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0_56) ),
    inference(subtyping,[status(esa)],[c_1383])).

cnf(c_322,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X5,X6,X7)
    | X6 != X2
    | X4 != X0
    | X5 != X1
    | X7 != X3 ),
    theory(equality)).

cnf(c_318,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_317,plain,
    ( ~ v1_pre_topc(X0)
    | v1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_314,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_310,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X5 != X2
    | X3 != X0
    | X4 != X1 ),
    theory(equality)).

cnf(c_306,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | r1_funct_2(X6,X7,X8,X9,X10,X11)
    | X8 != X2
    | X6 != X0
    | X7 != X1
    | X9 != X3
    | X10 != X4
    | X11 != X5 ),
    theory(equality)).

cnf(c_304,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_302,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2829,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_353,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_3,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_410,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_pre_topc(X6,X7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v2_pre_topc(X7)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_struct_0(X7)
    | v2_struct_0(X6)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | ~ l1_pre_topc(X7)
    | X3 = X0
    | k9_tmap_1(X7,X6) != X0
    | k3_struct_0(X7) != X3
    | u1_struct_0(X7) != X5
    | u1_struct_0(X7) != X4
    | u1_struct_0(X7) != X1
    | u1_struct_0(k8_tmap_1(X7,X6)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_411,plain,
    ( ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_16,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_415,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k3_struct_0(X0))
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_16,c_353])).

cnf(c_416,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(renaming,[status(thm)],[c_415])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_445,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_416,c_17,c_15])).

cnf(c_866,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = k3_struct_0(X0)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_445,c_25])).

cnf(c_867,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ l1_pre_topc(sK1)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_866])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_869,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_867,c_29,c_28,c_27,c_26])).

cnf(c_870,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_869])).

cnf(c_1103,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_353,c_870])).

cnf(c_966,plain,
    ( l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_964,c_29,c_28,c_27])).

cnf(c_1526,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(X0)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k8_tmap_1(sK1,sK2) != X0
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_1103,c_966])).

cnf(c_1527,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1526])).

cnf(c_10,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1245,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(sK1,sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_955])).

cnf(c_1246,plain,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_1245])).

cnf(c_1250,plain,
    ( v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1246,c_29,c_28,c_27,c_964])).

cnf(c_1251,plain,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_1250])).

cnf(c_1623,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) != k3_struct_0(sK1)
    | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) != u1_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_1527,c_1251])).

cnf(c_2805,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56) != k3_struct_0(sK1)
    | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) != u1_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_1623])).

cnf(c_2825,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | sP0_iProver_split
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2805])).

cnf(c_3242,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_struct_0(sK1)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2825])).

cnf(c_2909,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_struct_0(sK1)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2825])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_908,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_25])).

cnf(c_909,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_908])).

cnf(c_911,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_909,c_27])).

cnf(c_2819,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_911])).

cnf(c_3229,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2819])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1266,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_1267,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1266])).

cnf(c_1271,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1267,c_29,c_27])).

cnf(c_2815,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0_56)) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_1271])).

cnf(c_3232,plain,
    ( u1_struct_0(k6_tmap_1(sK1,X0_56)) = u1_struct_0(sK1)
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2815])).

cnf(c_3506,plain,
    ( u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_3229,c_3232])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_194,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_22,c_14,c_13,c_12])).

cnf(c_195,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_194])).

cnf(c_900,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_195,c_25])).

cnf(c_901,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_903,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_901,c_29,c_28,c_27])).

cnf(c_2820,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_903])).

cnf(c_3507,plain,
    ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_3506,c_2820])).

cnf(c_4309,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_struct_0(sK1)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3242,c_2909,c_3507])).

cnf(c_1227,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_28])).

cnf(c_1228,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1227])).

cnf(c_1232,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1228,c_29,c_27])).

cnf(c_1559,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k7_tmap_1(sK1,X0) != k3_struct_0(sK1)
    | u1_struct_0(k6_tmap_1(sK1,X0)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_1527,c_1232])).

cnf(c_1563,plain,
    ( k7_tmap_1(sK1,X0) != k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1559,c_29,c_27,c_1267])).

cnf(c_1564,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k7_tmap_1(sK1,X0) != k3_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1563])).

cnf(c_2236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k7_tmap_1(sK1,X0) != k3_struct_0(sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_1564])).

cnf(c_2803,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k7_tmap_1(sK1,X0_56) != k3_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_2236])).

cnf(c_2828,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | sP1_iProver_split
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2803])).

cnf(c_3246,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_struct_0(sK1)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2828])).

cnf(c_1503,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(X0)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1103,c_27])).

cnf(c_1504,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(sK1)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1503])).

cnf(c_1506,plain,
    ( ~ v1_funct_1(k3_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1504,c_29])).

cnf(c_1507,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1506])).

cnf(c_1591,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k7_tmap_1(sK1,X0) != k3_struct_0(sK1)
    | u1_struct_0(k6_tmap_1(sK1,X0)) != u1_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_1507,c_1232])).

cnf(c_1595,plain,
    ( k7_tmap_1(sK1,X0) != k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | ~ v1_funct_1(k3_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1591,c_29,c_27,c_1267])).

cnf(c_1596,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k7_tmap_1(sK1,X0) != k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1595])).

cnf(c_2232,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k7_tmap_1(sK1,X0) != k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_1596])).

cnf(c_2804,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k7_tmap_1(sK1,X0_56) != k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_2232])).

cnf(c_2827,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | sP1_iProver_split
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2804])).

cnf(c_2913,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_struct_0(sK1)) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2827])).

cnf(c_4300,plain,
    ( v1_funct_1(k3_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | sP1_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3246,c_2913,c_3507])).

cnf(c_4301,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_struct_0(sK1)) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(renaming,[status(thm)],[c_4300])).

cnf(c_2824,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56) != k3_struct_0(sK1)
    | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) != u1_struct_0(sK1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_2805])).

cnf(c_3243,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56) != k3_struct_0(sK1)
    | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) != u1_struct_0(sK1)
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2824])).

cnf(c_4233,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56) != k3_struct_0(sK1)
    | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) != u1_struct_0(sK1)
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3243,c_3507])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1338,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_28])).

cnf(c_1339,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1338])).

cnf(c_1343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1339,c_29,c_27])).

cnf(c_2811,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,X0_56) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1343])).

cnf(c_3236,plain,
    ( k7_tmap_1(sK1,X0_56) = k6_partfun1(u1_struct_0(sK1))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2811])).

cnf(c_3554,plain,
    ( k7_tmap_1(sK1,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_3229,c_3236])).

cnf(c_2826,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,X0_56) != k3_struct_0(sK1)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_2804])).

cnf(c_3245,plain,
    ( k7_tmap_1(sK1,X0_56) != k3_struct_0(sK1)
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2826])).

cnf(c_4157,plain,
    ( k6_partfun1(u1_struct_0(sK1)) != k3_struct_0(sK1)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3554,c_3245])).

cnf(c_32,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_910,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_909])).

cnf(c_4226,plain,
    ( k6_partfun1(u1_struct_0(sK1)) != k3_struct_0(sK1)
    | sP1_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4157,c_32,c_910])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_955])).

cnf(c_1420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_1419])).

cnf(c_1424,plain,
    ( v2_struct_0(k8_tmap_1(sK1,sK2))
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1420,c_29,c_28,c_27,c_964])).

cnf(c_1425,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_1424])).

cnf(c_2807,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)))))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_1425])).

cnf(c_3240,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56))))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2807])).

cnf(c_4082,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56))))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3240,c_3507])).

cnf(c_3238,plain,
    ( u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0_56)
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2809])).

cnf(c_4029,plain,
    ( u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0_56)
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3238,c_3507])).

cnf(c_4036,plain,
    ( u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2))) = k5_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3229,c_4029])).

cnf(c_1440,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_955])).

cnf(c_1441,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(unflattening,[status(thm)],[c_1440])).

cnf(c_1445,plain,
    ( v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1441,c_29,c_28,c_27,c_964])).

cnf(c_1446,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(renaming,[status(thm)],[c_1445])).

cnf(c_2806,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_1446])).

cnf(c_3241,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2806])).

cnf(c_3958,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56) = k6_partfun1(u1_struct_0(sK1))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3241,c_3507])).

cnf(c_3965,plain,
    ( k7_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK1))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3229,c_3958])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_955])).

cnf(c_1399,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_1398])).

cnf(c_1403,plain,
    ( v2_struct_0(k8_tmap_1(sK1,sK2))
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1399,c_29,c_28,c_27,c_964])).

cnf(c_1404,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_1403])).

cnf(c_2808,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56))
    | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_1404])).

cnf(c_3239,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2808])).

cnf(c_3950,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3239,c_3507])).

cnf(c_1356,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_19,c_955])).

cnf(c_1357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_1356])).

cnf(c_1361,plain,
    ( v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1357,c_29,c_28,c_27,c_964])).

cnf(c_1362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_1361])).

cnf(c_2810,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_1362])).

cnf(c_3237,plain,
    ( u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = u1_struct_0(k8_tmap_1(sK1,sK2))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2810])).

cnf(c_3885,plain,
    ( u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = u1_struct_0(sK1)
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3237,c_3507])).

cnf(c_3892,plain,
    ( u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2))) = u1_struct_0(sK1)
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3229,c_3885])).

cnf(c_1320,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_28])).

cnf(c_1321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1320])).

cnf(c_1325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1321,c_29,c_27])).

cnf(c_2812,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_56))))) ),
    inference(subtyping,[status(esa)],[c_1325])).

cnf(c_3235,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_56))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2812])).

cnf(c_3756,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3554,c_3235])).

cnf(c_3757,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3756,c_2820,c_3507])).

cnf(c_3760,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3757,c_32,c_910])).

cnf(c_20,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_176,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_22])).

cnf(c_177,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_176])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_371,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK1,sK2)
    | sK3 != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_177,c_23])).

cnf(c_372,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_376,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(sK2,X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_26,c_24])).

cnf(c_377,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(renaming,[status(thm)],[c_376])).

cnf(c_1055,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2)
    | sK1 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_377])).

cnf(c_1056,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(sK1,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_1055])).

cnf(c_379,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
    | k6_tmap_1(sK1,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_1058,plain,
    ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1056,c_29,c_28,c_27,c_25,c_379,c_901])).

cnf(c_2816,plain,
    ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
    inference(subtyping,[status(esa)],[c_1058])).

cnf(c_3284,plain,
    ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
    inference(light_normalisation,[status(thm)],[c_2816,c_2820])).

cnf(c_3750,plain,
    ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
    inference(demodulation,[status(thm)],[c_3554,c_3284])).

cnf(c_1302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_1303,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1302])).

cnf(c_1307,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1303,c_29,c_27])).

cnf(c_2813,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,X0_56)) ),
    inference(subtyping,[status(esa)],[c_1307])).

cnf(c_3234,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_56)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2813])).

cnf(c_3455,plain,
    ( v1_funct_1(k7_tmap_1(sK1,u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3229,c_3234])).

cnf(c_3749,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3554,c_3455])).

cnf(c_3233,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,X0_56)) = k5_tmap_1(sK1,X0_56)
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2814])).

cnf(c_3558,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2))) = k5_tmap_1(sK1,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_3229,c_3233])).

cnf(c_3559,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3558,c_2820])).

cnf(c_930,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_931,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_930])).

cnf(c_933,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_931,c_29,c_28,c_27])).

cnf(c_2817,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
    inference(subtyping,[status(esa)],[c_933])).

cnf(c_3231,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2817])).

cnf(c_3509,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3507,c_3231])).

cnf(c_919,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_920,plain,
    ( ~ v2_pre_topc(sK1)
    | v1_funct_1(k9_tmap_1(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_919])).

cnf(c_922,plain,
    ( v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_920,c_29,c_28,c_27])).

cnf(c_2818,plain,
    ( v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_922])).

cnf(c_3230,plain,
    ( v1_funct_1(k9_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2818])).

cnf(c_2823,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3226,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2823])).

cnf(c_2822,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3227,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2822])).

cnf(c_2821,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_3228,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2821])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.52/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.04  
% 2.52/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/1.04  
% 2.52/1.04  ------  iProver source info
% 2.52/1.04  
% 2.52/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.52/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/1.04  git: non_committed_changes: false
% 2.52/1.04  git: last_make_outside_of_git: false
% 2.52/1.04  
% 2.52/1.04  ------ 
% 2.52/1.04  
% 2.52/1.04  ------ Input Options
% 2.52/1.04  
% 2.52/1.04  --out_options                           all
% 2.52/1.04  --tptp_safe_out                         true
% 2.52/1.04  --problem_path                          ""
% 2.52/1.04  --include_path                          ""
% 2.52/1.04  --clausifier                            res/vclausify_rel
% 2.52/1.04  --clausifier_options                    --mode clausify
% 2.52/1.04  --stdin                                 false
% 2.52/1.04  --stats_out                             all
% 2.52/1.04  
% 2.52/1.04  ------ General Options
% 2.52/1.04  
% 2.52/1.04  --fof                                   false
% 2.52/1.04  --time_out_real                         305.
% 2.52/1.04  --time_out_virtual                      -1.
% 2.52/1.04  --symbol_type_check                     false
% 2.52/1.04  --clausify_out                          false
% 2.52/1.04  --sig_cnt_out                           false
% 2.52/1.04  --trig_cnt_out                          false
% 2.52/1.04  --trig_cnt_out_tolerance                1.
% 2.52/1.04  --trig_cnt_out_sk_spl                   false
% 2.52/1.04  --abstr_cl_out                          false
% 2.52/1.04  
% 2.52/1.04  ------ Global Options
% 2.52/1.04  
% 2.52/1.04  --schedule                              default
% 2.52/1.04  --add_important_lit                     false
% 2.52/1.04  --prop_solver_per_cl                    1000
% 2.52/1.04  --min_unsat_core                        false
% 2.52/1.04  --soft_assumptions                      false
% 2.52/1.04  --soft_lemma_size                       3
% 2.52/1.04  --prop_impl_unit_size                   0
% 2.52/1.04  --prop_impl_unit                        []
% 2.52/1.04  --share_sel_clauses                     true
% 2.52/1.04  --reset_solvers                         false
% 2.52/1.04  --bc_imp_inh                            [conj_cone]
% 2.52/1.04  --conj_cone_tolerance                   3.
% 2.52/1.04  --extra_neg_conj                        none
% 2.52/1.04  --large_theory_mode                     true
% 2.52/1.04  --prolific_symb_bound                   200
% 2.52/1.04  --lt_threshold                          2000
% 2.52/1.04  --clause_weak_htbl                      true
% 2.52/1.04  --gc_record_bc_elim                     false
% 2.52/1.04  
% 2.52/1.04  ------ Preprocessing Options
% 2.52/1.04  
% 2.52/1.04  --preprocessing_flag                    true
% 2.52/1.04  --time_out_prep_mult                    0.1
% 2.52/1.04  --splitting_mode                        input
% 2.52/1.04  --splitting_grd                         true
% 2.52/1.04  --splitting_cvd                         false
% 2.52/1.04  --splitting_cvd_svl                     false
% 2.52/1.04  --splitting_nvd                         32
% 2.52/1.04  --sub_typing                            true
% 2.52/1.04  --prep_gs_sim                           true
% 2.52/1.04  --prep_unflatten                        true
% 2.52/1.04  --prep_res_sim                          true
% 2.52/1.04  --prep_upred                            true
% 2.52/1.04  --prep_sem_filter                       exhaustive
% 2.52/1.04  --prep_sem_filter_out                   false
% 2.52/1.04  --pred_elim                             true
% 2.52/1.04  --res_sim_input                         true
% 2.52/1.04  --eq_ax_congr_red                       true
% 2.52/1.04  --pure_diseq_elim                       true
% 2.52/1.04  --brand_transform                       false
% 2.52/1.04  --non_eq_to_eq                          false
% 2.52/1.04  --prep_def_merge                        true
% 2.52/1.04  --prep_def_merge_prop_impl              false
% 2.52/1.04  --prep_def_merge_mbd                    true
% 2.52/1.04  --prep_def_merge_tr_red                 false
% 2.52/1.04  --prep_def_merge_tr_cl                  false
% 2.52/1.04  --smt_preprocessing                     true
% 2.52/1.04  --smt_ac_axioms                         fast
% 2.52/1.04  --preprocessed_out                      false
% 2.52/1.04  --preprocessed_stats                    false
% 2.52/1.04  
% 2.52/1.04  ------ Abstraction refinement Options
% 2.52/1.04  
% 2.52/1.04  --abstr_ref                             []
% 2.52/1.04  --abstr_ref_prep                        false
% 2.52/1.04  --abstr_ref_until_sat                   false
% 2.52/1.04  --abstr_ref_sig_restrict                funpre
% 2.52/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/1.04  --abstr_ref_under                       []
% 2.52/1.04  
% 2.52/1.04  ------ SAT Options
% 2.52/1.04  
% 2.52/1.04  --sat_mode                              false
% 2.52/1.04  --sat_fm_restart_options                ""
% 2.52/1.04  --sat_gr_def                            false
% 2.52/1.04  --sat_epr_types                         true
% 2.52/1.04  --sat_non_cyclic_types                  false
% 2.52/1.04  --sat_finite_models                     false
% 2.52/1.04  --sat_fm_lemmas                         false
% 2.52/1.04  --sat_fm_prep                           false
% 2.52/1.04  --sat_fm_uc_incr                        true
% 2.52/1.04  --sat_out_model                         small
% 2.52/1.04  --sat_out_clauses                       false
% 2.52/1.04  
% 2.52/1.04  ------ QBF Options
% 2.52/1.04  
% 2.52/1.04  --qbf_mode                              false
% 2.52/1.04  --qbf_elim_univ                         false
% 2.52/1.04  --qbf_dom_inst                          none
% 2.52/1.04  --qbf_dom_pre_inst                      false
% 2.52/1.04  --qbf_sk_in                             false
% 2.52/1.04  --qbf_pred_elim                         true
% 2.52/1.04  --qbf_split                             512
% 2.52/1.04  
% 2.52/1.04  ------ BMC1 Options
% 2.52/1.04  
% 2.52/1.04  --bmc1_incremental                      false
% 2.52/1.04  --bmc1_axioms                           reachable_all
% 2.52/1.04  --bmc1_min_bound                        0
% 2.52/1.04  --bmc1_max_bound                        -1
% 2.52/1.04  --bmc1_max_bound_default                -1
% 2.52/1.04  --bmc1_symbol_reachability              true
% 2.52/1.04  --bmc1_property_lemmas                  false
% 2.52/1.04  --bmc1_k_induction                      false
% 2.52/1.04  --bmc1_non_equiv_states                 false
% 2.52/1.04  --bmc1_deadlock                         false
% 2.52/1.04  --bmc1_ucm                              false
% 2.52/1.04  --bmc1_add_unsat_core                   none
% 2.52/1.04  --bmc1_unsat_core_children              false
% 2.52/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/1.04  --bmc1_out_stat                         full
% 2.52/1.04  --bmc1_ground_init                      false
% 2.52/1.04  --bmc1_pre_inst_next_state              false
% 2.52/1.04  --bmc1_pre_inst_state                   false
% 2.52/1.04  --bmc1_pre_inst_reach_state             false
% 2.52/1.04  --bmc1_out_unsat_core                   false
% 2.52/1.04  --bmc1_aig_witness_out                  false
% 2.52/1.04  --bmc1_verbose                          false
% 2.52/1.04  --bmc1_dump_clauses_tptp                false
% 2.52/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.52/1.04  --bmc1_dump_file                        -
% 2.52/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.52/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.52/1.04  --bmc1_ucm_extend_mode                  1
% 2.52/1.04  --bmc1_ucm_init_mode                    2
% 2.52/1.04  --bmc1_ucm_cone_mode                    none
% 2.52/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.52/1.04  --bmc1_ucm_relax_model                  4
% 2.52/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.52/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/1.04  --bmc1_ucm_layered_model                none
% 2.52/1.04  --bmc1_ucm_max_lemma_size               10
% 2.52/1.04  
% 2.52/1.04  ------ AIG Options
% 2.52/1.04  
% 2.52/1.04  --aig_mode                              false
% 2.52/1.04  
% 2.52/1.04  ------ Instantiation Options
% 2.52/1.04  
% 2.52/1.04  --instantiation_flag                    true
% 2.52/1.04  --inst_sos_flag                         false
% 2.52/1.04  --inst_sos_phase                        true
% 2.52/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/1.04  --inst_lit_sel_side                     num_symb
% 2.52/1.04  --inst_solver_per_active                1400
% 2.52/1.04  --inst_solver_calls_frac                1.
% 2.52/1.04  --inst_passive_queue_type               priority_queues
% 2.52/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/1.04  --inst_passive_queues_freq              [25;2]
% 2.52/1.04  --inst_dismatching                      true
% 2.52/1.04  --inst_eager_unprocessed_to_passive     true
% 2.52/1.04  --inst_prop_sim_given                   true
% 2.52/1.04  --inst_prop_sim_new                     false
% 2.52/1.04  --inst_subs_new                         false
% 2.52/1.04  --inst_eq_res_simp                      false
% 2.52/1.04  --inst_subs_given                       false
% 2.52/1.04  --inst_orphan_elimination               true
% 2.52/1.04  --inst_learning_loop_flag               true
% 2.52/1.04  --inst_learning_start                   3000
% 2.52/1.04  --inst_learning_factor                  2
% 2.52/1.04  --inst_start_prop_sim_after_learn       3
% 2.52/1.04  --inst_sel_renew                        solver
% 2.52/1.04  --inst_lit_activity_flag                true
% 2.52/1.04  --inst_restr_to_given                   false
% 2.52/1.04  --inst_activity_threshold               500
% 2.52/1.04  --inst_out_proof                        true
% 2.52/1.04  
% 2.52/1.04  ------ Resolution Options
% 2.52/1.04  
% 2.52/1.04  --resolution_flag                       true
% 2.52/1.04  --res_lit_sel                           adaptive
% 2.52/1.04  --res_lit_sel_side                      none
% 2.52/1.04  --res_ordering                          kbo
% 2.52/1.04  --res_to_prop_solver                    active
% 2.52/1.04  --res_prop_simpl_new                    false
% 2.52/1.04  --res_prop_simpl_given                  true
% 2.52/1.04  --res_passive_queue_type                priority_queues
% 2.52/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/1.04  --res_passive_queues_freq               [15;5]
% 2.52/1.04  --res_forward_subs                      full
% 2.52/1.04  --res_backward_subs                     full
% 2.52/1.04  --res_forward_subs_resolution           true
% 2.52/1.04  --res_backward_subs_resolution          true
% 2.52/1.04  --res_orphan_elimination                true
% 2.52/1.04  --res_time_limit                        2.
% 2.52/1.04  --res_out_proof                         true
% 2.52/1.04  
% 2.52/1.04  ------ Superposition Options
% 2.52/1.04  
% 2.52/1.04  --superposition_flag                    true
% 2.52/1.04  --sup_passive_queue_type                priority_queues
% 2.52/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.52/1.04  --demod_completeness_check              fast
% 2.52/1.04  --demod_use_ground                      true
% 2.52/1.04  --sup_to_prop_solver                    passive
% 2.52/1.04  --sup_prop_simpl_new                    true
% 2.52/1.04  --sup_prop_simpl_given                  true
% 2.52/1.04  --sup_fun_splitting                     false
% 2.52/1.04  --sup_smt_interval                      50000
% 2.52/1.04  
% 2.52/1.04  ------ Superposition Simplification Setup
% 2.52/1.04  
% 2.52/1.04  --sup_indices_passive                   []
% 2.52/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.04  --sup_full_bw                           [BwDemod]
% 2.52/1.04  --sup_immed_triv                        [TrivRules]
% 2.52/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.04  --sup_immed_bw_main                     []
% 2.52/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.04  
% 2.52/1.04  ------ Combination Options
% 2.52/1.04  
% 2.52/1.04  --comb_res_mult                         3
% 2.52/1.04  --comb_sup_mult                         2
% 2.52/1.04  --comb_inst_mult                        10
% 2.52/1.04  
% 2.52/1.04  ------ Debug Options
% 2.52/1.04  
% 2.52/1.04  --dbg_backtrace                         false
% 2.52/1.04  --dbg_dump_prop_clauses                 false
% 2.52/1.04  --dbg_dump_prop_clauses_file            -
% 2.52/1.04  --dbg_out_stat                          false
% 2.52/1.04  ------ Parsing...
% 2.52/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/1.04  
% 2.52/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.52/1.04  
% 2.52/1.04  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/1.04  
% 2.52/1.04  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.52/1.04  ------ Proving...
% 2.52/1.04  ------ Problem Properties 
% 2.52/1.04  
% 2.52/1.04  
% 2.52/1.04  clauses                                 24
% 2.52/1.04  conjectures                             3
% 2.52/1.04  EPR                                     2
% 2.52/1.04  Horn                                    16
% 2.52/1.04  unary                                   8
% 2.52/1.04  binary                                  5
% 2.52/1.04  lits                                    59
% 2.52/1.04  lits eq                                 17
% 2.52/1.04  fd_pure                                 0
% 2.52/1.04  fd_pseudo                               0
% 2.52/1.04  fd_cond                                 0
% 2.52/1.04  fd_pseudo_cond                          0
% 2.52/1.04  AC symbols                              0
% 2.52/1.04  
% 2.52/1.04  ------ Schedule dynamic 5 is on 
% 2.52/1.04  
% 2.52/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.52/1.04  
% 2.52/1.04  
% 2.52/1.04  ------ 
% 2.52/1.04  Current options:
% 2.52/1.04  ------ 
% 2.52/1.04  
% 2.52/1.04  ------ Input Options
% 2.52/1.04  
% 2.52/1.04  --out_options                           all
% 2.52/1.04  --tptp_safe_out                         true
% 2.52/1.04  --problem_path                          ""
% 2.52/1.04  --include_path                          ""
% 2.52/1.04  --clausifier                            res/vclausify_rel
% 2.52/1.04  --clausifier_options                    --mode clausify
% 2.52/1.04  --stdin                                 false
% 2.52/1.04  --stats_out                             all
% 2.52/1.04  
% 2.52/1.04  ------ General Options
% 2.52/1.04  
% 2.52/1.04  --fof                                   false
% 2.52/1.04  --time_out_real                         305.
% 2.52/1.04  --time_out_virtual                      -1.
% 2.52/1.04  --symbol_type_check                     false
% 2.52/1.04  --clausify_out                          false
% 2.52/1.04  --sig_cnt_out                           false
% 2.52/1.04  --trig_cnt_out                          false
% 2.52/1.04  --trig_cnt_out_tolerance                1.
% 2.52/1.04  --trig_cnt_out_sk_spl                   false
% 2.52/1.04  --abstr_cl_out                          false
% 2.52/1.04  
% 2.52/1.04  ------ Global Options
% 2.52/1.04  
% 2.52/1.04  --schedule                              default
% 2.52/1.04  --add_important_lit                     false
% 2.52/1.04  --prop_solver_per_cl                    1000
% 2.52/1.04  --min_unsat_core                        false
% 2.52/1.04  --soft_assumptions                      false
% 2.52/1.04  --soft_lemma_size                       3
% 2.52/1.04  --prop_impl_unit_size                   0
% 2.52/1.04  --prop_impl_unit                        []
% 2.52/1.04  --share_sel_clauses                     true
% 2.52/1.04  --reset_solvers                         false
% 2.52/1.04  --bc_imp_inh                            [conj_cone]
% 2.52/1.04  --conj_cone_tolerance                   3.
% 2.52/1.04  --extra_neg_conj                        none
% 2.52/1.04  --large_theory_mode                     true
% 2.52/1.04  --prolific_symb_bound                   200
% 2.52/1.04  --lt_threshold                          2000
% 2.52/1.04  --clause_weak_htbl                      true
% 2.52/1.04  --gc_record_bc_elim                     false
% 2.52/1.04  
% 2.52/1.04  ------ Preprocessing Options
% 2.52/1.04  
% 2.52/1.04  --preprocessing_flag                    true
% 2.52/1.04  --time_out_prep_mult                    0.1
% 2.52/1.04  --splitting_mode                        input
% 2.52/1.04  --splitting_grd                         true
% 2.52/1.04  --splitting_cvd                         false
% 2.52/1.04  --splitting_cvd_svl                     false
% 2.52/1.04  --splitting_nvd                         32
% 2.52/1.04  --sub_typing                            true
% 2.52/1.04  --prep_gs_sim                           true
% 2.52/1.04  --prep_unflatten                        true
% 2.52/1.04  --prep_res_sim                          true
% 2.52/1.04  --prep_upred                            true
% 2.52/1.04  --prep_sem_filter                       exhaustive
% 2.52/1.04  --prep_sem_filter_out                   false
% 2.52/1.04  --pred_elim                             true
% 2.52/1.04  --res_sim_input                         true
% 2.52/1.04  --eq_ax_congr_red                       true
% 2.52/1.04  --pure_diseq_elim                       true
% 2.52/1.04  --brand_transform                       false
% 2.52/1.04  --non_eq_to_eq                          false
% 2.52/1.04  --prep_def_merge                        true
% 2.52/1.04  --prep_def_merge_prop_impl              false
% 2.52/1.04  --prep_def_merge_mbd                    true
% 2.52/1.04  --prep_def_merge_tr_red                 false
% 2.52/1.04  --prep_def_merge_tr_cl                  false
% 2.52/1.04  --smt_preprocessing                     true
% 2.52/1.04  --smt_ac_axioms                         fast
% 2.52/1.04  --preprocessed_out                      false
% 2.52/1.04  --preprocessed_stats                    false
% 2.52/1.04  
% 2.52/1.04  ------ Abstraction refinement Options
% 2.52/1.04  
% 2.52/1.04  --abstr_ref                             []
% 2.52/1.04  --abstr_ref_prep                        false
% 2.52/1.04  --abstr_ref_until_sat                   false
% 2.52/1.04  --abstr_ref_sig_restrict                funpre
% 2.52/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/1.04  --abstr_ref_under                       []
% 2.52/1.04  
% 2.52/1.04  ------ SAT Options
% 2.52/1.04  
% 2.52/1.04  --sat_mode                              false
% 2.52/1.04  --sat_fm_restart_options                ""
% 2.52/1.04  --sat_gr_def                            false
% 2.52/1.04  --sat_epr_types                         true
% 2.52/1.04  --sat_non_cyclic_types                  false
% 2.52/1.04  --sat_finite_models                     false
% 2.52/1.04  --sat_fm_lemmas                         false
% 2.52/1.04  --sat_fm_prep                           false
% 2.52/1.04  --sat_fm_uc_incr                        true
% 2.52/1.04  --sat_out_model                         small
% 2.52/1.04  --sat_out_clauses                       false
% 2.52/1.04  
% 2.52/1.04  ------ QBF Options
% 2.52/1.04  
% 2.52/1.04  --qbf_mode                              false
% 2.52/1.04  --qbf_elim_univ                         false
% 2.52/1.04  --qbf_dom_inst                          none
% 2.52/1.04  --qbf_dom_pre_inst                      false
% 2.52/1.04  --qbf_sk_in                             false
% 2.52/1.04  --qbf_pred_elim                         true
% 2.52/1.04  --qbf_split                             512
% 2.52/1.04  
% 2.52/1.04  ------ BMC1 Options
% 2.52/1.04  
% 2.52/1.04  --bmc1_incremental                      false
% 2.52/1.04  --bmc1_axioms                           reachable_all
% 2.52/1.04  --bmc1_min_bound                        0
% 2.52/1.04  --bmc1_max_bound                        -1
% 2.52/1.04  --bmc1_max_bound_default                -1
% 2.52/1.04  --bmc1_symbol_reachability              true
% 2.52/1.04  --bmc1_property_lemmas                  false
% 2.52/1.04  --bmc1_k_induction                      false
% 2.52/1.04  --bmc1_non_equiv_states                 false
% 2.52/1.04  --bmc1_deadlock                         false
% 2.52/1.04  --bmc1_ucm                              false
% 2.52/1.04  --bmc1_add_unsat_core                   none
% 2.52/1.04  --bmc1_unsat_core_children              false
% 2.52/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/1.04  --bmc1_out_stat                         full
% 2.52/1.04  --bmc1_ground_init                      false
% 2.52/1.04  --bmc1_pre_inst_next_state              false
% 2.52/1.04  --bmc1_pre_inst_state                   false
% 2.52/1.04  --bmc1_pre_inst_reach_state             false
% 2.52/1.04  --bmc1_out_unsat_core                   false
% 2.52/1.04  --bmc1_aig_witness_out                  false
% 2.52/1.04  --bmc1_verbose                          false
% 2.52/1.04  --bmc1_dump_clauses_tptp                false
% 2.52/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.52/1.04  --bmc1_dump_file                        -
% 2.52/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.52/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.52/1.04  --bmc1_ucm_extend_mode                  1
% 2.52/1.04  --bmc1_ucm_init_mode                    2
% 2.52/1.04  --bmc1_ucm_cone_mode                    none
% 2.52/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.52/1.04  --bmc1_ucm_relax_model                  4
% 2.52/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.52/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/1.04  --bmc1_ucm_layered_model                none
% 2.52/1.04  --bmc1_ucm_max_lemma_size               10
% 2.52/1.04  
% 2.52/1.04  ------ AIG Options
% 2.52/1.04  
% 2.52/1.04  --aig_mode                              false
% 2.52/1.04  
% 2.52/1.04  ------ Instantiation Options
% 2.52/1.04  
% 2.52/1.04  --instantiation_flag                    true
% 2.52/1.04  --inst_sos_flag                         false
% 2.52/1.04  --inst_sos_phase                        true
% 2.52/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/1.04  --inst_lit_sel_side                     none
% 2.52/1.04  --inst_solver_per_active                1400
% 2.52/1.04  --inst_solver_calls_frac                1.
% 2.52/1.04  --inst_passive_queue_type               priority_queues
% 2.52/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/1.04  --inst_passive_queues_freq              [25;2]
% 2.52/1.04  --inst_dismatching                      true
% 2.52/1.04  --inst_eager_unprocessed_to_passive     true
% 2.52/1.04  --inst_prop_sim_given                   true
% 2.52/1.04  --inst_prop_sim_new                     false
% 2.52/1.04  --inst_subs_new                         false
% 2.52/1.04  --inst_eq_res_simp                      false
% 2.52/1.04  --inst_subs_given                       false
% 2.52/1.04  --inst_orphan_elimination               true
% 2.52/1.04  --inst_learning_loop_flag               true
% 2.52/1.04  --inst_learning_start                   3000
% 2.52/1.04  --inst_learning_factor                  2
% 2.52/1.04  --inst_start_prop_sim_after_learn       3
% 2.52/1.04  --inst_sel_renew                        solver
% 2.52/1.04  --inst_lit_activity_flag                true
% 2.52/1.04  --inst_restr_to_given                   false
% 2.52/1.04  --inst_activity_threshold               500
% 2.52/1.04  --inst_out_proof                        true
% 2.52/1.04  
% 2.52/1.04  ------ Resolution Options
% 2.52/1.04  
% 2.52/1.04  --resolution_flag                       false
% 2.52/1.04  --res_lit_sel                           adaptive
% 2.52/1.04  --res_lit_sel_side                      none
% 2.52/1.04  --res_ordering                          kbo
% 2.52/1.04  --res_to_prop_solver                    active
% 2.52/1.04  --res_prop_simpl_new                    false
% 2.52/1.04  --res_prop_simpl_given                  true
% 2.52/1.04  --res_passive_queue_type                priority_queues
% 2.52/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/1.04  --res_passive_queues_freq               [15;5]
% 2.52/1.04  --res_forward_subs                      full
% 2.52/1.04  --res_backward_subs                     full
% 2.52/1.04  --res_forward_subs_resolution           true
% 2.52/1.04  --res_backward_subs_resolution          true
% 2.52/1.04  --res_orphan_elimination                true
% 2.52/1.04  --res_time_limit                        2.
% 2.52/1.04  --res_out_proof                         true
% 2.52/1.04  
% 2.52/1.04  ------ Superposition Options
% 2.52/1.04  
% 2.52/1.04  --superposition_flag                    true
% 2.52/1.04  --sup_passive_queue_type                priority_queues
% 2.52/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.52/1.04  --demod_completeness_check              fast
% 2.52/1.04  --demod_use_ground                      true
% 2.52/1.04  --sup_to_prop_solver                    passive
% 2.52/1.04  --sup_prop_simpl_new                    true
% 2.52/1.04  --sup_prop_simpl_given                  true
% 2.52/1.04  --sup_fun_splitting                     false
% 2.52/1.04  --sup_smt_interval                      50000
% 2.52/1.04  
% 2.52/1.04  ------ Superposition Simplification Setup
% 2.52/1.04  
% 2.52/1.04  --sup_indices_passive                   []
% 2.52/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.04  --sup_full_bw                           [BwDemod]
% 2.52/1.04  --sup_immed_triv                        [TrivRules]
% 2.52/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.04  --sup_immed_bw_main                     []
% 2.52/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.04  
% 2.52/1.04  ------ Combination Options
% 2.52/1.04  
% 2.52/1.04  --comb_res_mult                         3
% 2.52/1.04  --comb_sup_mult                         2
% 2.52/1.04  --comb_inst_mult                        10
% 2.52/1.04  
% 2.52/1.04  ------ Debug Options
% 2.52/1.04  
% 2.52/1.04  --dbg_backtrace                         false
% 2.52/1.04  --dbg_dump_prop_clauses                 false
% 2.52/1.04  --dbg_dump_prop_clauses_file            -
% 2.52/1.04  --dbg_out_stat                          false
% 2.52/1.04  
% 2.52/1.04  
% 2.52/1.04  
% 2.52/1.04  
% 2.52/1.04  ------ Proving...
% 2.52/1.04  
% 2.52/1.04  
% 2.52/1.04  % SZS status CounterSatisfiable for theBenchmark.p
% 2.52/1.04  
% 2.52/1.04  % SZS output start Saturation for theBenchmark.p
% 2.52/1.04  
% 2.52/1.04  fof(f9,axiom,(
% 2.52/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.52/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.04  
% 2.52/1.04  fof(f30,plain,(
% 2.52/1.04    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.52/1.04    inference(ennf_transformation,[],[f9])).
% 2.52/1.04  
% 2.52/1.04  fof(f31,plain,(
% 2.52/1.04    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.04    inference(flattening,[],[f30])).
% 2.52/1.04  
% 2.52/1.04  fof(f67,plain,(
% 2.52/1.04    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f31])).
% 2.52/1.04  
% 2.52/1.04  fof(f13,conjecture,(
% 2.52/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 2.52/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.04  
% 2.52/1.04  fof(f14,negated_conjecture,(
% 2.52/1.04    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 2.52/1.04    inference(negated_conjecture,[],[f13])).
% 2.52/1.04  
% 2.52/1.04  fof(f37,plain,(
% 2.52/1.04    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.52/1.04    inference(ennf_transformation,[],[f14])).
% 2.52/1.04  
% 2.52/1.04  fof(f38,plain,(
% 2.52/1.04    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.52/1.04    inference(flattening,[],[f37])).
% 2.52/1.04  
% 2.52/1.04  fof(f46,plain,(
% 2.52/1.04    ( ! [X0,X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) => (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK3) & m1_subset_1(sK3,u1_struct_0(X1)))) )),
% 2.52/1.04    introduced(choice_axiom,[])).
% 2.52/1.04  
% 2.52/1.04  fof(f45,plain,(
% 2.52/1.04    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tmap_1(sK2,k8_tmap_1(X0,sK2),k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.52/1.04    introduced(choice_axiom,[])).
% 2.52/1.04  
% 2.52/1.04  fof(f44,plain,(
% 2.52/1.04    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(sK1,X1),k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.52/1.04    introduced(choice_axiom,[])).
% 2.52/1.04  
% 2.52/1.04  fof(f47,plain,(
% 2.52/1.04    ((~r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2))) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.52/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f46,f45,f44])).
% 2.52/1.04  
% 2.52/1.04  fof(f72,plain,(
% 2.52/1.04    v2_pre_topc(sK1)),
% 2.52/1.04    inference(cnf_transformation,[],[f47])).
% 2.52/1.04  
% 2.52/1.04  fof(f71,plain,(
% 2.52/1.04    ~v2_struct_0(sK1)),
% 2.52/1.04    inference(cnf_transformation,[],[f47])).
% 2.52/1.04  
% 2.52/1.04  fof(f73,plain,(
% 2.52/1.04    l1_pre_topc(sK1)),
% 2.52/1.04    inference(cnf_transformation,[],[f47])).
% 2.52/1.04  
% 2.52/1.04  fof(f7,axiom,(
% 2.52/1.04    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 2.52/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.04  
% 2.52/1.04  fof(f26,plain,(
% 2.52/1.04    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.52/1.04    inference(ennf_transformation,[],[f7])).
% 2.52/1.04  
% 2.52/1.04  fof(f27,plain,(
% 2.52/1.04    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.04    inference(flattening,[],[f26])).
% 2.52/1.04  
% 2.52/1.04  fof(f61,plain,(
% 2.52/1.04    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f27])).
% 2.52/1.04  
% 2.52/1.04  fof(f75,plain,(
% 2.52/1.04    m1_pre_topc(sK2,sK1)),
% 2.52/1.04    inference(cnf_transformation,[],[f47])).
% 2.52/1.04  
% 2.52/1.04  fof(f62,plain,(
% 2.52/1.04    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f27])).
% 2.52/1.04  
% 2.52/1.04  fof(f1,axiom,(
% 2.52/1.04    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.52/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.04  
% 2.52/1.04  fof(f15,plain,(
% 2.52/1.04    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.52/1.04    inference(ennf_transformation,[],[f1])).
% 2.52/1.04  
% 2.52/1.04  fof(f48,plain,(
% 2.52/1.04    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f15])).
% 2.52/1.04  
% 2.52/1.04  fof(f2,axiom,(
% 2.52/1.04    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.52/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.04  
% 2.52/1.04  fof(f16,plain,(
% 2.52/1.04    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.52/1.04    inference(ennf_transformation,[],[f2])).
% 2.52/1.04  
% 2.52/1.04  fof(f17,plain,(
% 2.52/1.04    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.52/1.04    inference(flattening,[],[f16])).
% 2.52/1.04  
% 2.52/1.04  fof(f49,plain,(
% 2.52/1.04    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f17])).
% 2.52/1.04  
% 2.52/1.04  fof(f3,axiom,(
% 2.52/1.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.52/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.04  
% 2.52/1.04  fof(f18,plain,(
% 2.52/1.04    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.52/1.04    inference(ennf_transformation,[],[f3])).
% 2.52/1.04  
% 2.52/1.04  fof(f19,plain,(
% 2.52/1.04    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.52/1.04    inference(flattening,[],[f18])).
% 2.52/1.04  
% 2.52/1.04  fof(f39,plain,(
% 2.52/1.04    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.52/1.04    inference(nnf_transformation,[],[f19])).
% 2.52/1.04  
% 2.52/1.04  fof(f50,plain,(
% 2.52/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f39])).
% 2.52/1.04  
% 2.52/1.04  fof(f11,axiom,(
% 2.52/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))))),
% 2.52/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.04  
% 2.52/1.04  fof(f34,plain,(
% 2.52/1.04    ! [X0] : (! [X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.52/1.04    inference(ennf_transformation,[],[f11])).
% 2.52/1.04  
% 2.52/1.04  fof(f35,plain,(
% 2.52/1.04    ! [X0] : (! [X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.04    inference(flattening,[],[f34])).
% 2.52/1.04  
% 2.52/1.04  fof(f69,plain,(
% 2.52/1.04    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f35])).
% 2.52/1.04  
% 2.52/1.04  fof(f8,axiom,(
% 2.52/1.04    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 2.52/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.04  
% 2.52/1.04  fof(f28,plain,(
% 2.52/1.04    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.52/1.04    inference(ennf_transformation,[],[f8])).
% 2.52/1.04  
% 2.52/1.04  fof(f29,plain,(
% 2.52/1.04    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.04    inference(flattening,[],[f28])).
% 2.52/1.04  
% 2.52/1.04  fof(f64,plain,(
% 2.52/1.04    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f29])).
% 2.52/1.04  
% 2.52/1.04  fof(f63,plain,(
% 2.52/1.04    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f29])).
% 2.52/1.04  
% 2.52/1.04  fof(f65,plain,(
% 2.52/1.04    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f29])).
% 2.52/1.04  
% 2.52/1.04  fof(f74,plain,(
% 2.52/1.04    ~v2_struct_0(sK2)),
% 2.52/1.04    inference(cnf_transformation,[],[f47])).
% 2.52/1.04  
% 2.52/1.04  fof(f6,axiom,(
% 2.52/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 2.52/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.04  
% 2.52/1.04  fof(f24,plain,(
% 2.52/1.04    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.52/1.04    inference(ennf_transformation,[],[f6])).
% 2.52/1.04  
% 2.52/1.04  fof(f25,plain,(
% 2.52/1.04    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.04    inference(flattening,[],[f24])).
% 2.52/1.04  
% 2.52/1.04  fof(f58,plain,(
% 2.52/1.04    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f25])).
% 2.52/1.04  
% 2.52/1.04  fof(f12,axiom,(
% 2.52/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.52/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.04  
% 2.52/1.04  fof(f36,plain,(
% 2.52/1.04    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.52/1.04    inference(ennf_transformation,[],[f12])).
% 2.52/1.04  
% 2.52/1.04  fof(f70,plain,(
% 2.52/1.04    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f36])).
% 2.52/1.04  
% 2.52/1.04  fof(f66,plain,(
% 2.52/1.04    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f31])).
% 2.52/1.04  
% 2.52/1.04  fof(f5,axiom,(
% 2.52/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 2.52/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.04  
% 2.52/1.04  fof(f22,plain,(
% 2.52/1.04    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.52/1.04    inference(ennf_transformation,[],[f5])).
% 2.52/1.04  
% 2.52/1.04  fof(f23,plain,(
% 2.52/1.04    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.04    inference(flattening,[],[f22])).
% 2.52/1.04  
% 2.52/1.04  fof(f40,plain,(
% 2.52/1.04    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.04    inference(nnf_transformation,[],[f23])).
% 2.52/1.04  
% 2.52/1.04  fof(f41,plain,(
% 2.52/1.04    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.04    inference(rectify,[],[f40])).
% 2.52/1.04  
% 2.52/1.04  fof(f42,plain,(
% 2.52/1.04    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.52/1.04    introduced(choice_axiom,[])).
% 2.52/1.04  
% 2.52/1.04  fof(f43,plain,(
% 2.52/1.04    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 2.52/1.04  
% 2.52/1.04  fof(f53,plain,(
% 2.52/1.04    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f43])).
% 2.52/1.04  
% 2.52/1.04  fof(f79,plain,(
% 2.52/1.04    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(equality_resolution,[],[f53])).
% 2.52/1.04  
% 2.52/1.04  fof(f80,plain,(
% 2.52/1.04    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(equality_resolution,[],[f79])).
% 2.52/1.04  
% 2.52/1.04  fof(f60,plain,(
% 2.52/1.04    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f27])).
% 2.52/1.04  
% 2.52/1.04  fof(f4,axiom,(
% 2.52/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 2.52/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.04  
% 2.52/1.04  fof(f20,plain,(
% 2.52/1.04    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.52/1.04    inference(ennf_transformation,[],[f4])).
% 2.52/1.04  
% 2.52/1.04  fof(f21,plain,(
% 2.52/1.04    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.04    inference(flattening,[],[f20])).
% 2.52/1.04  
% 2.52/1.04  fof(f52,plain,(
% 2.52/1.04    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f21])).
% 2.52/1.04  
% 2.52/1.04  fof(f59,plain,(
% 2.52/1.04    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f25])).
% 2.52/1.04  
% 2.52/1.04  fof(f57,plain,(
% 2.52/1.04    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f25])).
% 2.52/1.04  
% 2.52/1.04  fof(f10,axiom,(
% 2.52/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(X2) = X1 => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 2.52/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.04  
% 2.52/1.04  fof(f32,plain,(
% 2.52/1.04    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.52/1.04    inference(ennf_transformation,[],[f10])).
% 2.52/1.04  
% 2.52/1.04  fof(f33,plain,(
% 2.52/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.52/1.04    inference(flattening,[],[f32])).
% 2.52/1.04  
% 2.52/1.04  fof(f68,plain,(
% 2.52/1.04    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(cnf_transformation,[],[f33])).
% 2.52/1.04  
% 2.52/1.04  fof(f81,plain,(
% 2.52/1.04    ( ! [X2,X0,X3] : (r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.52/1.04    inference(equality_resolution,[],[f68])).
% 2.52/1.04  
% 2.52/1.04  fof(f77,plain,(
% 2.52/1.04    ~r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK3)),
% 2.52/1.04    inference(cnf_transformation,[],[f47])).
% 2.52/1.04  
% 2.52/1.04  fof(f76,plain,(
% 2.52/1.04    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.52/1.04    inference(cnf_transformation,[],[f47])).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2850,plain,
% 2.52/1.04      ( k5_tmap_1(X0_57,X0_56) = k5_tmap_1(X1_57,X0_56) | X0_57 != X1_57 ),
% 2.52/1.04      theory(equality) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2849,plain,
% 2.52/1.04      ( u1_pre_topc(X0_57) = u1_pre_topc(X1_57) | X0_57 != X1_57 ),
% 2.52/1.04      theory(equality) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2836,plain,
% 2.52/1.04      ( X0_58 != X1_58 | X2_58 != X1_58 | X2_58 = X0_58 ),
% 2.52/1.04      theory(equality) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2832,plain,( X0_58 = X0_58 ),theory(equality) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_18,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 2.52/1.04      inference(cnf_transformation,[],[f67]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_28,negated_conjecture,
% 2.52/1.04      ( v2_pre_topc(sK1) ),
% 2.52/1.04      inference(cnf_transformation,[],[f72]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1284,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
% 2.52/1.04      | sK1 != X1 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1285,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | ~ l1_pre_topc(sK1)
% 2.52/1.04      | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1284]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_29,negated_conjecture,
% 2.52/1.04      ( ~ v2_struct_0(sK1) ),
% 2.52/1.04      inference(cnf_transformation,[],[f71]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_27,negated_conjecture,
% 2.52/1.04      ( l1_pre_topc(sK1) ),
% 2.52/1.04      inference(cnf_transformation,[],[f73]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1289,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1285,c_29,c_27]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2814,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | u1_pre_topc(k6_tmap_1(sK1,X0_56)) = k5_tmap_1(sK1,X0_56) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_1289]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_13,plain,
% 2.52/1.04      ( ~ m1_pre_topc(X0,X1)
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v2_pre_topc(k8_tmap_1(X1,X0))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1) ),
% 2.52/1.04      inference(cnf_transformation,[],[f61]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_25,negated_conjecture,
% 2.52/1.04      ( m1_pre_topc(sK2,sK1) ),
% 2.52/1.04      inference(cnf_transformation,[],[f75]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_952,plain,
% 2.52/1.04      ( ~ v2_pre_topc(X0)
% 2.52/1.04      | v2_pre_topc(k8_tmap_1(X0,X1))
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | sK1 != X0
% 2.52/1.04      | sK2 != X1 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_953,plain,
% 2.52/1.04      ( v2_pre_topc(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | ~ v2_pre_topc(sK1)
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | ~ l1_pre_topc(sK1) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_952]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_955,plain,
% 2.52/1.04      ( v2_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_953,c_29,c_28,c_27]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1377,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | k8_tmap_1(sK1,sK2) != X1
% 2.52/1.04      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_18,c_955]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1378,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1377]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_12,plain,
% 2.52/1.04      ( ~ m1_pre_topc(X0,X1)
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.52/1.04      inference(cnf_transformation,[],[f62]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_963,plain,
% 2.52/1.04      ( ~ v2_pre_topc(X0)
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | l1_pre_topc(k8_tmap_1(X0,X1))
% 2.52/1.04      | sK1 != X0
% 2.52/1.04      | sK2 != X1 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_964,plain,
% 2.52/1.04      ( ~ v2_pre_topc(sK1)
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | ~ l1_pre_topc(sK1) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_963]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1382,plain,
% 2.52/1.04      ( v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1378,c_29,c_28,c_27,c_964]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1383,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0) ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_1382]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2809,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0_56) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_1383]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_322,plain,
% 2.52/1.04      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.52/1.04      | r1_tmap_1(X4,X5,X6,X7)
% 2.52/1.04      | X6 != X2
% 2.52/1.04      | X4 != X0
% 2.52/1.04      | X5 != X1
% 2.52/1.04      | X7 != X3 ),
% 2.52/1.04      theory(equality) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_318,plain,
% 2.52/1.04      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.52/1.04      theory(equality) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_317,plain,
% 2.52/1.04      ( ~ v1_pre_topc(X0) | v1_pre_topc(X1) | X1 != X0 ),
% 2.52/1.04      theory(equality) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_314,plain,
% 2.52/1.04      ( ~ v2_pre_topc(X0) | v2_pre_topc(X1) | X1 != X0 ),
% 2.52/1.04      theory(equality) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_310,plain,
% 2.52/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 2.52/1.04      | v1_funct_2(X3,X4,X5)
% 2.52/1.04      | X5 != X2
% 2.52/1.04      | X3 != X0
% 2.52/1.04      | X4 != X1 ),
% 2.52/1.04      theory(equality) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_306,plain,
% 2.52/1.04      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 2.52/1.04      | r1_funct_2(X6,X7,X8,X9,X10,X11)
% 2.52/1.04      | X8 != X2
% 2.52/1.04      | X6 != X0
% 2.52/1.04      | X7 != X1
% 2.52/1.04      | X9 != X3
% 2.52/1.04      | X10 != X4
% 2.52/1.04      | X11 != X5 ),
% 2.52/1.04      theory(equality) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_304,plain,
% 2.52/1.04      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.52/1.04      theory(equality) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_302,plain,
% 2.52/1.04      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 2.52/1.04      theory(equality) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2829,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_0,plain,
% 2.52/1.04      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.52/1.04      inference(cnf_transformation,[],[f48]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1,plain,
% 2.52/1.04      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 2.52/1.04      inference(cnf_transformation,[],[f49]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_353,plain,
% 2.52/1.04      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) ),
% 2.52/1.04      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3,plain,
% 2.52/1.04      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 2.52/1.04      | ~ v1_funct_2(X5,X2,X3)
% 2.52/1.04      | ~ v1_funct_2(X4,X0,X1)
% 2.52/1.04      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.52/1.04      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.52/1.04      | ~ v1_funct_1(X5)
% 2.52/1.04      | ~ v1_funct_1(X4)
% 2.52/1.04      | v1_xboole_0(X1)
% 2.52/1.04      | v1_xboole_0(X3)
% 2.52/1.04      | X4 = X5 ),
% 2.52/1.04      inference(cnf_transformation,[],[f50]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_21,plain,
% 2.52/1.04      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
% 2.52/1.04      | ~ m1_pre_topc(X1,X0)
% 2.52/1.04      | ~ v2_pre_topc(X0)
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X0) ),
% 2.52/1.04      inference(cnf_transformation,[],[f69]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_410,plain,
% 2.52/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 2.52/1.04      | ~ v1_funct_2(X3,X4,X5)
% 2.52/1.04      | ~ m1_pre_topc(X6,X7)
% 2.52/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/1.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.52/1.04      | ~ v2_pre_topc(X7)
% 2.52/1.04      | ~ v1_funct_1(X0)
% 2.52/1.04      | ~ v1_funct_1(X3)
% 2.52/1.04      | v2_struct_0(X7)
% 2.52/1.04      | v2_struct_0(X6)
% 2.52/1.04      | v1_xboole_0(X2)
% 2.52/1.04      | v1_xboole_0(X5)
% 2.52/1.04      | ~ l1_pre_topc(X7)
% 2.52/1.04      | X3 = X0
% 2.52/1.04      | k9_tmap_1(X7,X6) != X0
% 2.52/1.04      | k3_struct_0(X7) != X3
% 2.52/1.04      | u1_struct_0(X7) != X5
% 2.52/1.04      | u1_struct_0(X7) != X4
% 2.52/1.04      | u1_struct_0(X7) != X1
% 2.52/1.04      | u1_struct_0(k8_tmap_1(X7,X6)) != X2 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_411,plain,
% 2.52/1.04      ( ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.52/1.04      | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.52/1.04      | ~ m1_pre_topc(X1,X0)
% 2.52/1.04      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.52/1.04      | ~ v2_pre_topc(X0)
% 2.52/1.04      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(X0))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | v1_xboole_0(u1_struct_0(X0))
% 2.52/1.04      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_410]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_16,plain,
% 2.52/1.04      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.52/1.04      | ~ m1_pre_topc(X1,X0)
% 2.52/1.04      | ~ v2_pre_topc(X0)
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | ~ l1_pre_topc(X0) ),
% 2.52/1.04      inference(cnf_transformation,[],[f64]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_415,plain,
% 2.52/1.04      ( v2_struct_0(X0)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(X0))
% 2.52/1.04      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.52/1.04      | ~ v2_pre_topc(X0)
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.52/1.04      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.52/1.04      | ~ m1_pre_topc(X1,X0)
% 2.52/1.04      | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.52/1.04      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_411,c_16,c_353]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_416,plain,
% 2.52/1.04      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.52/1.04      | ~ m1_pre_topc(X1,X0)
% 2.52/1.04      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.52/1.04      | ~ v2_pre_topc(X0)
% 2.52/1.04      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(X0))
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_415]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_17,plain,
% 2.52/1.04      ( ~ m1_pre_topc(X0,X1)
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v1_funct_1(k9_tmap_1(X1,X0))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1) ),
% 2.52/1.04      inference(cnf_transformation,[],[f63]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_15,plain,
% 2.52/1.04      ( ~ m1_pre_topc(X0,X1)
% 2.52/1.04      | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1) ),
% 2.52/1.04      inference(cnf_transformation,[],[f65]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_445,plain,
% 2.52/1.04      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.52/1.04      | ~ m1_pre_topc(X1,X0)
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.52/1.04      | ~ v2_pre_topc(X0)
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(X0))
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 2.52/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_416,c_17,c_15]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_866,plain,
% 2.52/1.04      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.52/1.04      | ~ v2_pre_topc(X0)
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(X0))
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | k9_tmap_1(X0,X1) = k3_struct_0(X0)
% 2.52/1.04      | sK1 != X0
% 2.52/1.04      | sK2 != X1 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_445,c_25]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_867,plain,
% 2.52/1.04      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v2_pre_topc(sK1)
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | v2_struct_0(sK2)
% 2.52/1.04      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.52/1.04      | ~ l1_pre_topc(sK1)
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_866]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_26,negated_conjecture,
% 2.52/1.04      ( ~ v2_struct_0(sK2) ),
% 2.52/1.04      inference(cnf_transformation,[],[f74]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_869,plain,
% 2.52/1.04      ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_867,c_29,c_28,c_27,c_26]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_870,plain,
% 2.52/1.04      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_869]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1103,plain,
% 2.52/1.04      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0) ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_353,c_870]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_966,plain,
% 2.52/1.04      ( l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_964,c_29,c_28,c_27]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1526,plain,
% 2.52/1.04      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | k8_tmap_1(sK1,sK2) != X0
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0) ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_1103,c_966]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1527,plain,
% 2.52/1.04      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1526]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_10,plain,
% 2.52/1.04      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.52/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.52/1.04      | ~ v2_pre_topc(X0)
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | ~ l1_pre_topc(X0) ),
% 2.52/1.04      inference(cnf_transformation,[],[f58]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1245,plain,
% 2.52/1.04      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.52/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | k8_tmap_1(sK1,sK2) != X0 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_10,c_955]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1246,plain,
% 2.52/1.04      ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))
% 2.52/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1245]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1250,plain,
% 2.52/1.04      ( v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0))) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1246,c_29,c_28,c_27,c_964]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1251,plain,
% 2.52/1.04      ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))
% 2.52/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_1250]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1623,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) != k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) != u1_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_1527,c_1251]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2805,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56) != k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) != u1_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_1623]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2825,plain,
% 2.52/1.04      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | sP0_iProver_split
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(splitting,
% 2.52/1.04                [splitting(split),new_symbols(definition,[])],
% 2.52/1.04                [c_2805]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3242,plain,
% 2.52/1.04      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 2.52/1.04      | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.52/1.04      | v1_funct_1(k3_struct_0(sK1)) != iProver_top
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top
% 2.52/1.04      | sP0_iProver_split = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2825]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2909,plain,
% 2.52/1.04      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 2.52/1.04      | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.52/1.04      | v1_funct_1(k3_struct_0(sK1)) != iProver_top
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top
% 2.52/1.04      | sP0_iProver_split = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2825]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_22,plain,
% 2.52/1.04      ( ~ m1_pre_topc(X0,X1)
% 2.52/1.04      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | ~ l1_pre_topc(X1) ),
% 2.52/1.04      inference(cnf_transformation,[],[f70]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_908,plain,
% 2.52/1.04      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | sK1 != X1
% 2.52/1.04      | sK2 != X0 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_22,c_25]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_909,plain,
% 2.52/1.04      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | ~ l1_pre_topc(sK1) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_908]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_911,plain,
% 2.52/1.04      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.52/1.04      inference(global_propositional_subsumption,[status(thm)],[c_909,c_27]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2819,plain,
% 2.52/1.04      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_911]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3229,plain,
% 2.52/1.04      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2819]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_19,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.52/1.04      inference(cnf_transformation,[],[f66]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1266,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 2.52/1.04      | sK1 != X1 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1267,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | ~ l1_pre_topc(sK1)
% 2.52/1.04      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1266]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1271,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1267,c_29,c_27]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2815,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | u1_struct_0(k6_tmap_1(sK1,X0_56)) = u1_struct_0(sK1) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_1271]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3232,plain,
% 2.52/1.04      ( u1_struct_0(k6_tmap_1(sK1,X0_56)) = u1_struct_0(sK1)
% 2.52/1.04      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2815]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3506,plain,
% 2.52/1.04      ( u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))) = u1_struct_0(sK1) ),
% 2.52/1.04      inference(superposition,[status(thm)],[c_3229,c_3232]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_8,plain,
% 2.52/1.04      ( ~ m1_pre_topc(X0,X1)
% 2.52/1.04      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 2.52/1.04      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.52/1.04      inference(cnf_transformation,[],[f80]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_14,plain,
% 2.52/1.04      ( ~ m1_pre_topc(X0,X1)
% 2.52/1.04      | v1_pre_topc(k8_tmap_1(X1,X0))
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1) ),
% 2.52/1.04      inference(cnf_transformation,[],[f60]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_194,plain,
% 2.52/1.04      ( ~ l1_pre_topc(X1)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ m1_pre_topc(X0,X1)
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_8,c_22,c_14,c_13,c_12]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_195,plain,
% 2.52/1.04      ( ~ m1_pre_topc(X0,X1)
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_194]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_900,plain,
% 2.52/1.04      ( ~ v2_pre_topc(X0)
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 2.52/1.04      | sK1 != X0
% 2.52/1.04      | sK2 != X1 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_195,c_25]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_901,plain,
% 2.52/1.04      ( ~ v2_pre_topc(sK1)
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | ~ l1_pre_topc(sK1)
% 2.52/1.04      | k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_900]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_903,plain,
% 2.52/1.04      ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_901,c_29,c_28,c_27]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2820,plain,
% 2.52/1.04      ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_903]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3507,plain,
% 2.52/1.04      ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.52/1.04      inference(light_normalisation,[status(thm)],[c_3506,c_2820]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_4309,plain,
% 2.52/1.04      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.52/1.04      | v1_funct_1(k3_struct_0(sK1)) != iProver_top
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top
% 2.52/1.04      | sP0_iProver_split = iProver_top ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_3242,c_2909,c_3507]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1227,plain,
% 2.52/1.04      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.52/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | sK1 != X0 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_10,c_28]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1228,plain,
% 2.52/1.04      ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
% 2.52/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | ~ l1_pre_topc(sK1) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1227]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1232,plain,
% 2.52/1.04      ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
% 2.52/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1228,c_29,c_27]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1559,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | k7_tmap_1(sK1,X0) != k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k6_tmap_1(sK1,X0)) != u1_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_1527,c_1232]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1563,plain,
% 2.52/1.04      ( k7_tmap_1(sK1,X0) != k3_struct_0(sK1)
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1559,c_29,c_27,c_1267]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1564,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | k7_tmap_1(sK1,X0) != k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_1563]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2236,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | k7_tmap_1(sK1,X0) != k3_struct_0(sK1) ),
% 2.52/1.04      inference(equality_resolution_simp,[status(thm)],[c_1564]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2803,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | k7_tmap_1(sK1,X0_56) != k3_struct_0(sK1) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_2236]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2828,plain,
% 2.52/1.04      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | sP1_iProver_split
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 2.52/1.04      inference(splitting,
% 2.52/1.04                [splitting(split),new_symbols(definition,[])],
% 2.52/1.04                [c_2803]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3246,plain,
% 2.52/1.04      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.52/1.04      | v1_funct_1(k3_struct_0(sK1)) != iProver_top
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top
% 2.52/1.04      | sP1_iProver_split = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2828]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1503,plain,
% 2.52/1.04      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0)
% 2.52/1.04      | sK1 != X0 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_1103,c_27]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1504,plain,
% 2.52/1.04      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1503]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1506,plain,
% 2.52/1.04      ( ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(global_propositional_subsumption,[status(thm)],[c_1504,c_29]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1507,plain,
% 2.52/1.04      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_1506]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1591,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | k7_tmap_1(sK1,X0) != k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k6_tmap_1(sK1,X0)) != u1_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_1507,c_1232]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1595,plain,
% 2.52/1.04      ( k7_tmap_1(sK1,X0) != k3_struct_0(sK1)
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1591,c_29,c_27,c_1267]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1596,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | k7_tmap_1(sK1,X0) != k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_1595]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2232,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | k7_tmap_1(sK1,X0) != k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(equality_resolution_simp,[status(thm)],[c_1596]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2804,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | k7_tmap_1(sK1,X0_56) != k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_2232]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2827,plain,
% 2.52/1.04      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.52/1.04      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.52/1.04      | sP1_iProver_split
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.52/1.04      inference(splitting,
% 2.52/1.04                [splitting(split),new_symbols(definition,[])],
% 2.52/1.04                [c_2804]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2913,plain,
% 2.52/1.04      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 2.52/1.04      | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.52/1.04      | v1_funct_1(k3_struct_0(sK1)) != iProver_top
% 2.52/1.04      | sP1_iProver_split = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2827]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_4300,plain,
% 2.52/1.04      ( v1_funct_1(k3_struct_0(sK1)) != iProver_top
% 2.52/1.04      | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.52/1.04      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | sP1_iProver_split = iProver_top ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_3246,c_2913,c_3507]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_4301,plain,
% 2.52/1.04      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.52/1.04      | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.52/1.04      | v1_funct_1(k3_struct_0(sK1)) != iProver_top
% 2.52/1.04      | sP1_iProver_split = iProver_top ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_4300]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2824,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56) != k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) != u1_struct_0(sK1)
% 2.52/1.04      | ~ sP0_iProver_split ),
% 2.52/1.04      inference(splitting,
% 2.52/1.04                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.52/1.04                [c_2805]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3243,plain,
% 2.52/1.04      ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56) != k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) != u1_struct_0(sK1)
% 2.52/1.04      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
% 2.52/1.04      | sP0_iProver_split != iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2824]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_4233,plain,
% 2.52/1.04      ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56) != k3_struct_0(sK1)
% 2.52/1.04      | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) != u1_struct_0(sK1)
% 2.52/1.04      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.52/1.04      | sP0_iProver_split != iProver_top ),
% 2.52/1.04      inference(light_normalisation,[status(thm)],[c_3243,c_3507]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_4,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 2.52/1.04      inference(cnf_transformation,[],[f52]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1338,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 2.52/1.04      | sK1 != X1 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_4,c_28]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1339,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | ~ l1_pre_topc(sK1)
% 2.52/1.04      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1338]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1343,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1339,c_29,c_27]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2811,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | k7_tmap_1(sK1,X0_56) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_1343]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3236,plain,
% 2.52/1.04      ( k7_tmap_1(sK1,X0_56) = k6_partfun1(u1_struct_0(sK1))
% 2.52/1.04      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2811]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3554,plain,
% 2.52/1.04      ( k7_tmap_1(sK1,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.52/1.04      inference(superposition,[status(thm)],[c_3229,c_3236]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2826,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | k7_tmap_1(sK1,X0_56) != k3_struct_0(sK1)
% 2.52/1.04      | ~ sP1_iProver_split ),
% 2.52/1.04      inference(splitting,
% 2.52/1.04                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.52/1.04                [c_2804]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3245,plain,
% 2.52/1.04      ( k7_tmap_1(sK1,X0_56) != k3_struct_0(sK1)
% 2.52/1.04      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.52/1.04      | sP1_iProver_split != iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2826]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_4157,plain,
% 2.52/1.04      ( k6_partfun1(u1_struct_0(sK1)) != k3_struct_0(sK1)
% 2.52/1.04      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.52/1.04      | sP1_iProver_split != iProver_top ),
% 2.52/1.04      inference(superposition,[status(thm)],[c_3554,c_3245]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_32,plain,
% 2.52/1.04      ( l1_pre_topc(sK1) = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_910,plain,
% 2.52/1.04      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.52/1.04      | l1_pre_topc(sK1) != iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_909]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_4226,plain,
% 2.52/1.04      ( k6_partfun1(u1_struct_0(sK1)) != k3_struct_0(sK1)
% 2.52/1.04      | sP1_iProver_split != iProver_top ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_4157,c_32,c_910]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_9,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1) ),
% 2.52/1.04      inference(cnf_transformation,[],[f59]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1419,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | k8_tmap_1(sK1,sK2) != X1 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_955]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1420,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1419]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1424,plain,
% 2.52/1.04      ( v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))))
% 2.52/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1420,c_29,c_28,c_27,c_964]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1425,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)))))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_1424]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2807,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)))))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_1425]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3240,plain,
% 2.52/1.04      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
% 2.52/1.04      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56))))) = iProver_top
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2807]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_4082,plain,
% 2.52/1.04      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.52/1.04      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56))))) = iProver_top
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.04      inference(light_normalisation,[status(thm)],[c_3240,c_3507]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3238,plain,
% 2.52/1.04      ( u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0_56)
% 2.52/1.04      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2809]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_4029,plain,
% 2.52/1.04      ( u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = k5_tmap_1(k8_tmap_1(sK1,sK2),X0_56)
% 2.52/1.04      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.04      inference(light_normalisation,[status(thm)],[c_3238,c_3507]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_4036,plain,
% 2.52/1.04      ( u1_pre_topc(k6_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2))) = k5_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.04      inference(superposition,[status(thm)],[c_3229,c_4029]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1440,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | k8_tmap_1(sK1,sK2) != X1
% 2.52/1.04      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_4,c_955]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1441,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1440]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1445,plain,
% 2.52/1.04      ( v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1441,c_29,c_28,c_27,c_964]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1446,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | k7_tmap_1(k8_tmap_1(sK1,sK2),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_1445]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2806,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_1446]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3241,plain,
% 2.52/1.04      ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56) = k6_partfun1(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.52/1.04      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2806]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3958,plain,
% 2.52/1.04      ( k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56) = k6_partfun1(u1_struct_0(sK1))
% 2.52/1.04      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.04      inference(light_normalisation,[status(thm)],[c_3241,c_3507]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3965,plain,
% 2.52/1.04      ( k7_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK1))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.04      inference(superposition,[status(thm)],[c_3229,c_3958]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_11,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1) ),
% 2.52/1.04      inference(cnf_transformation,[],[f57]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1398,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | k8_tmap_1(sK1,sK2) != X1 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_11,c_955]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1399,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1398]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1403,plain,
% 2.52/1.04      ( v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0))
% 2.52/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1399,c_29,c_28,c_27,c_964]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1404,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_1403]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2808,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_1404]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3239,plain,
% 2.52/1.04      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
% 2.52/1.04      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = iProver_top
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2808]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3950,plain,
% 2.52/1.04      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.52/1.04      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = iProver_top
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.04      inference(light_normalisation,[status(thm)],[c_3239,c_3507]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1356,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | k8_tmap_1(sK1,sK2) != X1
% 2.52/1.04      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_19,c_955]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1357,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1356]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1361,plain,
% 2.52/1.04      ( v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1357,c_29,c_28,c_27,c_964]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1362,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_1361]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2810,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = u1_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_1362]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3237,plain,
% 2.52/1.04      ( u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = u1_struct_0(k8_tmap_1(sK1,sK2))
% 2.52/1.04      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2810]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3885,plain,
% 2.52/1.04      ( u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),X0_56)) = u1_struct_0(sK1)
% 2.52/1.04      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.04      inference(light_normalisation,[status(thm)],[c_3237,c_3507]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3892,plain,
% 2.52/1.04      ( u1_struct_0(k6_tmap_1(k8_tmap_1(sK1,sK2),u1_struct_0(sK2))) = u1_struct_0(sK1)
% 2.52/1.04      | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.04      inference(superposition,[status(thm)],[c_3229,c_3885]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1320,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | sK1 != X1 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_28]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1321,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))))
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | ~ l1_pre_topc(sK1) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1320]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1325,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0))))) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1321,c_29,c_27]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2812,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | m1_subset_1(k7_tmap_1(sK1,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_56))))) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_1325]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3235,plain,
% 2.52/1.04      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.52/1.04      | m1_subset_1(k7_tmap_1(sK1,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_56))))) = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2812]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3756,plain,
% 2.52/1.04      ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2)))))) = iProver_top
% 2.52/1.04      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.52/1.04      inference(superposition,[status(thm)],[c_3554,c_3235]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3757,plain,
% 2.52/1.04      ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top
% 2.52/1.04      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.52/1.04      inference(light_normalisation,[status(thm)],[c_3756,c_2820,c_3507]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3760,plain,
% 2.52/1.04      ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_3757,c_32,c_910]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_20,plain,
% 2.52/1.04      ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 2.52/1.04      | ~ m1_pre_topc(X0,X1)
% 2.52/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.52/1.04      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | ~ l1_pre_topc(X1) ),
% 2.52/1.04      inference(cnf_transformation,[],[f81]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_176,plain,
% 2.52/1.04      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.52/1.04      | ~ m1_pre_topc(X0,X1)
% 2.52/1.04      | r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | ~ l1_pre_topc(X1) ),
% 2.52/1.04      inference(global_propositional_subsumption,[status(thm)],[c_20,c_22]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_177,plain,
% 2.52/1.04      ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 2.52/1.04      | ~ m1_pre_topc(X0,X1)
% 2.52/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1) ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_176]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_23,negated_conjecture,
% 2.52/1.04      ( ~ r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK3) ),
% 2.52/1.04      inference(cnf_transformation,[],[f77]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_371,plain,
% 2.52/1.04      ( ~ m1_pre_topc(X0,X1)
% 2.52/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.52/1.04      | ~ v2_pre_topc(X1)
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.52/1.04      | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK1,sK2)
% 2.52/1.04      | sK3 != X2
% 2.52/1.04      | sK2 != X0 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_177,c_23]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_372,plain,
% 2.52/1.04      ( ~ m1_pre_topc(sK2,X0)
% 2.52/1.04      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.52/1.04      | ~ v2_pre_topc(X0)
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | v2_struct_0(sK2)
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.52/1.04      | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_371]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_24,negated_conjecture,
% 2.52/1.04      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.52/1.04      inference(cnf_transformation,[],[f76]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_376,plain,
% 2.52/1.04      ( v2_struct_0(X0)
% 2.52/1.04      | ~ v2_pre_topc(X0)
% 2.52/1.04      | ~ m1_pre_topc(sK2,X0)
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.52/1.04      | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_372,c_26,c_24]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_377,plain,
% 2.52/1.04      ( ~ m1_pre_topc(sK2,X0)
% 2.52/1.04      | ~ v2_pre_topc(X0)
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.52/1.04      | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 2.52/1.04      inference(renaming,[status(thm)],[c_376]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1055,plain,
% 2.52/1.04      ( ~ v2_pre_topc(X0)
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK2)),k7_tmap_1(X0,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.52/1.04      | k6_tmap_1(X0,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2)
% 2.52/1.04      | sK1 != X0
% 2.52/1.04      | sK2 != sK2 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_25,c_377]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1056,plain,
% 2.52/1.04      ( ~ v2_pre_topc(sK1)
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | ~ l1_pre_topc(sK1)
% 2.52/1.04      | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.52/1.04      | k6_tmap_1(sK1,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1055]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_379,plain,
% 2.52/1.04      ( ~ m1_pre_topc(sK2,sK1)
% 2.52/1.04      | ~ v2_pre_topc(sK1)
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | ~ l1_pre_topc(sK1)
% 2.52/1.04      | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)
% 2.52/1.04      | k6_tmap_1(sK1,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2) ),
% 2.52/1.04      inference(instantiation,[status(thm)],[c_377]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1058,plain,
% 2.52/1.04      ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1056,c_29,c_28,c_27,c_25,c_379,c_901]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2816,plain,
% 2.52/1.04      ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_1058]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3284,plain,
% 2.52/1.04      ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k7_tmap_1(sK1,u1_struct_0(sK2)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
% 2.52/1.04      inference(light_normalisation,[status(thm)],[c_2816,c_2820]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3750,plain,
% 2.52/1.04      ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK2) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) ),
% 2.52/1.04      inference(demodulation,[status(thm)],[c_3554,c_3284]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1302,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.04      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.52/1.04      | v2_struct_0(X1)
% 2.52/1.04      | ~ l1_pre_topc(X1)
% 2.52/1.04      | sK1 != X1 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_11,c_28]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1303,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | v1_funct_1(k7_tmap_1(sK1,X0))
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | ~ l1_pre_topc(sK1) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_1302]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_1307,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | v1_funct_1(k7_tmap_1(sK1,X0)) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_1303,c_29,c_27]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2813,plain,
% 2.52/1.04      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.04      | v1_funct_1(k7_tmap_1(sK1,X0_56)) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_1307]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3234,plain,
% 2.52/1.04      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.52/1.04      | v1_funct_1(k7_tmap_1(sK1,X0_56)) = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2813]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3455,plain,
% 2.52/1.04      ( v1_funct_1(k7_tmap_1(sK1,u1_struct_0(sK2))) = iProver_top ),
% 2.52/1.04      inference(superposition,[status(thm)],[c_3229,c_3234]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3749,plain,
% 2.52/1.04      ( v1_funct_1(k6_partfun1(u1_struct_0(sK1))) = iProver_top ),
% 2.52/1.04      inference(demodulation,[status(thm)],[c_3554,c_3455]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3233,plain,
% 2.52/1.04      ( u1_pre_topc(k6_tmap_1(sK1,X0_56)) = k5_tmap_1(sK1,X0_56)
% 2.52/1.04      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2814]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3558,plain,
% 2.52/1.04      ( u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2))) = k5_tmap_1(sK1,u1_struct_0(sK2)) ),
% 2.52/1.04      inference(superposition,[status(thm)],[c_3229,c_3233]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3559,plain,
% 2.52/1.04      ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(light_normalisation,[status(thm)],[c_3558,c_2820]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_930,plain,
% 2.52/1.04      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.52/1.04      | ~ v2_pre_topc(X0)
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | sK1 != X0
% 2.52/1.04      | sK2 != X1 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_931,plain,
% 2.52/1.04      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 2.52/1.04      | ~ v2_pre_topc(sK1)
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | ~ l1_pre_topc(sK1) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_930]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_933,plain,
% 2.52/1.04      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_931,c_29,c_28,c_27]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2817,plain,
% 2.52/1.04      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_933]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3231,plain,
% 2.52/1.04      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2817]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3509,plain,
% 2.52/1.04      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 2.52/1.04      inference(demodulation,[status(thm)],[c_3507,c_3231]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_919,plain,
% 2.52/1.04      ( ~ v2_pre_topc(X0)
% 2.52/1.04      | v1_funct_1(k9_tmap_1(X0,X1))
% 2.52/1.04      | v2_struct_0(X0)
% 2.52/1.04      | ~ l1_pre_topc(X0)
% 2.52/1.04      | sK1 != X0
% 2.52/1.04      | sK2 != X1 ),
% 2.52/1.04      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_920,plain,
% 2.52/1.04      ( ~ v2_pre_topc(sK1)
% 2.52/1.04      | v1_funct_1(k9_tmap_1(sK1,sK2))
% 2.52/1.04      | v2_struct_0(sK1)
% 2.52/1.04      | ~ l1_pre_topc(sK1) ),
% 2.52/1.04      inference(unflattening,[status(thm)],[c_919]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_922,plain,
% 2.52/1.04      ( v1_funct_1(k9_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(global_propositional_subsumption,
% 2.52/1.04                [status(thm)],
% 2.52/1.04                [c_920,c_29,c_28,c_27]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2818,plain,
% 2.52/1.04      ( v1_funct_1(k9_tmap_1(sK1,sK2)) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_922]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3230,plain,
% 2.52/1.04      ( v1_funct_1(k9_tmap_1(sK1,sK2)) = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2818]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2823,negated_conjecture,
% 2.52/1.04      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_24]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3226,plain,
% 2.52/1.04      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2823]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2822,negated_conjecture,
% 2.52/1.04      ( ~ v2_struct_0(sK2) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_26]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3227,plain,
% 2.52/1.04      ( v2_struct_0(sK2) != iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2822]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_2821,negated_conjecture,
% 2.52/1.04      ( ~ v2_struct_0(sK1) ),
% 2.52/1.04      inference(subtyping,[status(esa)],[c_29]) ).
% 2.52/1.04  
% 2.52/1.04  cnf(c_3228,plain,
% 2.52/1.04      ( v2_struct_0(sK1) != iProver_top ),
% 2.52/1.04      inference(predicate_to_equality,[status(thm)],[c_2821]) ).
% 2.52/1.04  
% 2.52/1.04  
% 2.52/1.04  % SZS output end Saturation for theBenchmark.p
% 2.52/1.04  
% 2.52/1.04  ------                               Statistics
% 2.52/1.04  
% 2.52/1.04  ------ General
% 2.52/1.04  
% 2.52/1.04  abstr_ref_over_cycles:                  0
% 2.52/1.04  abstr_ref_under_cycles:                 0
% 2.52/1.04  gc_basic_clause_elim:                   0
% 2.52/1.04  forced_gc_time:                         0
% 2.52/1.04  parsing_time:                           0.015
% 2.52/1.04  unif_index_cands_time:                  0.
% 2.52/1.04  unif_index_add_time:                    0.
% 2.52/1.04  orderings_time:                         0.
% 2.52/1.04  out_proof_time:                         0.
% 2.52/1.04  total_time:                             0.197
% 2.52/1.04  num_of_symbols:                         68
% 2.52/1.04  num_of_terms:                           3070
% 2.52/1.04  
% 2.52/1.04  ------ Preprocessing
% 2.52/1.04  
% 2.52/1.04  num_of_splits:                          3
% 2.52/1.04  num_of_split_atoms:                     2
% 2.52/1.04  num_of_reused_defs:                     1
% 2.52/1.04  num_eq_ax_congr_red:                    11
% 2.52/1.04  num_of_sem_filtered_clauses:            7
% 2.52/1.04  num_of_subtypes:                        4
% 2.52/1.04  monotx_restored_types:                  0
% 2.52/1.04  sat_num_of_epr_types:                   0
% 2.52/1.04  sat_num_of_non_cyclic_types:            0
% 2.52/1.04  sat_guarded_non_collapsed_types:        0
% 2.52/1.04  num_pure_diseq_elim:                    0
% 2.52/1.04  simp_replaced_by:                       0
% 2.52/1.04  res_preprocessed:                       138
% 2.52/1.04  prep_upred:                             0
% 2.52/1.04  prep_unflattend:                        59
% 2.52/1.04  smt_new_axioms:                         0
% 2.52/1.04  pred_elim_cands:                        3
% 2.52/1.04  pred_elim:                              9
% 2.52/1.04  pred_elim_cl:                           9
% 2.52/1.04  pred_elim_cycles:                       19
% 2.52/1.04  merged_defs:                            0
% 2.52/1.04  merged_defs_ncl:                        0
% 2.52/1.04  bin_hyper_res:                          0
% 2.52/1.04  prep_cycles:                            4
% 2.52/1.04  pred_elim_time:                         0.077
% 2.52/1.04  splitting_time:                         0.
% 2.52/1.04  sem_filter_time:                        0.
% 2.52/1.04  monotx_time:                            0.
% 2.52/1.04  subtype_inf_time:                       0.
% 2.52/1.04  
% 2.52/1.04  ------ Problem properties
% 2.52/1.04  
% 2.52/1.04  clauses:                                24
% 2.52/1.04  conjectures:                            3
% 2.52/1.04  epr:                                    2
% 2.52/1.04  horn:                                   16
% 2.52/1.04  ground:                                 11
% 2.52/1.04  unary:                                  8
% 2.52/1.04  binary:                                 5
% 2.52/1.04  lits:                                   59
% 2.52/1.04  lits_eq:                                17
% 2.52/1.04  fd_pure:                                0
% 2.52/1.04  fd_pseudo:                              0
% 2.52/1.04  fd_cond:                                0
% 2.52/1.04  fd_pseudo_cond:                         0
% 2.52/1.04  ac_symbols:                             0
% 2.52/1.04  
% 2.52/1.04  ------ Propositional Solver
% 2.52/1.04  
% 2.52/1.04  prop_solver_calls:                      27
% 2.52/1.04  prop_fast_solver_calls:                 1565
% 2.52/1.04  smt_solver_calls:                       0
% 2.52/1.04  smt_fast_solver_calls:                  0
% 2.52/1.04  prop_num_of_clauses:                    975
% 2.52/1.04  prop_preprocess_simplified:             4106
% 2.52/1.04  prop_fo_subsumed:                       75
% 2.52/1.04  prop_solver_time:                       0.
% 2.52/1.04  smt_solver_time:                        0.
% 2.52/1.04  smt_fast_solver_time:                   0.
% 2.52/1.04  prop_fast_solver_time:                  0.
% 2.52/1.04  prop_unsat_core_time:                   0.
% 2.52/1.04  
% 2.52/1.04  ------ QBF
% 2.52/1.04  
% 2.52/1.04  qbf_q_res:                              0
% 2.52/1.04  qbf_num_tautologies:                    0
% 2.52/1.04  qbf_prep_cycles:                        0
% 2.52/1.04  
% 2.52/1.04  ------ BMC1
% 2.52/1.04  
% 2.52/1.04  bmc1_current_bound:                     -1
% 2.52/1.04  bmc1_last_solved_bound:                 -1
% 2.52/1.04  bmc1_unsat_core_size:                   -1
% 2.52/1.04  bmc1_unsat_core_parents_size:           -1
% 2.52/1.04  bmc1_merge_next_fun:                    0
% 2.52/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.52/1.04  
% 2.52/1.04  ------ Instantiation
% 2.52/1.04  
% 2.52/1.04  inst_num_of_clauses:                    225
% 2.52/1.04  inst_num_in_passive:                    55
% 2.52/1.04  inst_num_in_active:                     170
% 2.52/1.04  inst_num_in_unprocessed:                0
% 2.52/1.04  inst_num_of_loops:                      180
% 2.52/1.04  inst_num_of_learning_restarts:          0
% 2.52/1.04  inst_num_moves_active_passive:          5
% 2.52/1.04  inst_lit_activity:                      0
% 2.52/1.04  inst_lit_activity_moves:                0
% 2.52/1.04  inst_num_tautologies:                   0
% 2.52/1.04  inst_num_prop_implied:                  0
% 2.52/1.04  inst_num_existing_simplified:           0
% 2.52/1.04  inst_num_eq_res_simplified:             0
% 2.52/1.04  inst_num_child_elim:                    0
% 2.52/1.04  inst_num_of_dismatching_blockings:      32
% 2.52/1.04  inst_num_of_non_proper_insts:           222
% 2.52/1.04  inst_num_of_duplicates:                 0
% 2.52/1.04  inst_inst_num_from_inst_to_res:         0
% 2.52/1.04  inst_dismatching_checking_time:         0.
% 2.52/1.04  
% 2.52/1.04  ------ Resolution
% 2.52/1.04  
% 2.52/1.04  res_num_of_clauses:                     0
% 2.52/1.04  res_num_in_passive:                     0
% 2.52/1.04  res_num_in_active:                      0
% 2.52/1.04  res_num_of_loops:                       142
% 2.52/1.04  res_forward_subset_subsumed:            70
% 2.52/1.04  res_backward_subset_subsumed:           1
% 2.52/1.04  res_forward_subsumed:                   0
% 2.52/1.04  res_backward_subsumed:                  1
% 2.52/1.04  res_forward_subsumption_resolution:     8
% 2.52/1.04  res_backward_subsumption_resolution:    0
% 2.52/1.04  res_clause_to_clause_subsumption:       132
% 2.52/1.04  res_orphan_elimination:                 0
% 2.52/1.04  res_tautology_del:                      74
% 2.52/1.04  res_num_eq_res_simplified:              2
% 2.52/1.04  res_num_sel_changes:                    0
% 2.52/1.04  res_moves_from_active_to_pass:          0
% 2.52/1.04  
% 2.52/1.04  ------ Superposition
% 2.52/1.04  
% 2.52/1.04  sup_time_total:                         0.
% 2.52/1.04  sup_time_generating:                    0.
% 2.52/1.04  sup_time_sim_full:                      0.
% 2.52/1.04  sup_time_sim_immed:                     0.
% 2.52/1.04  
% 2.52/1.04  sup_num_of_clauses:                     31
% 2.52/1.04  sup_num_in_active:                      31
% 2.52/1.04  sup_num_in_passive:                     0
% 2.52/1.04  sup_num_of_loops:                       34
% 2.52/1.04  sup_fw_superposition:                   9
% 2.52/1.04  sup_bw_superposition:                   1
% 2.52/1.04  sup_immediate_simplified:               4
% 2.52/1.04  sup_given_eliminated:                   0
% 2.52/1.04  comparisons_done:                       0
% 2.52/1.04  comparisons_avoided:                    0
% 2.52/1.04  
% 2.52/1.04  ------ Simplifications
% 2.52/1.04  
% 2.52/1.04  
% 2.52/1.04  sim_fw_subset_subsumed:                 0
% 2.52/1.04  sim_bw_subset_subsumed:                 0
% 2.52/1.04  sim_fw_subsumed:                        0
% 2.52/1.04  sim_bw_subsumed:                        0
% 2.52/1.04  sim_fw_subsumption_res:                 0
% 2.52/1.04  sim_bw_subsumption_res:                 0
% 2.52/1.04  sim_tautology_del:                      0
% 2.52/1.04  sim_eq_tautology_del:                   0
% 2.52/1.04  sim_eq_res_simp:                        0
% 2.52/1.04  sim_fw_demodulated:                     0
% 2.52/1.04  sim_bw_demodulated:                     3
% 2.52/1.04  sim_light_normalised:                   12
% 2.52/1.04  sim_joinable_taut:                      0
% 2.52/1.04  sim_joinable_simp:                      0
% 2.52/1.04  sim_ac_normalised:                      0
% 2.52/1.04  sim_smt_subsumption:                    0
% 2.52/1.04  
%------------------------------------------------------------------------------
