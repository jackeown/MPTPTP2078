%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1780+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:23 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 570 expanded)
%              Number of clauses        :   92 ( 164 expanded)
%              Number of leaves         :   16 ( 165 expanded)
%              Depth                    :   26
%              Number of atoms          :  473 (3118 expanded)
%              Number of equality atoms :  126 ( 516 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) != X2
              & r2_hidden(X2,u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) != X2
              & r2_hidden(X2,u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k4_tmap_1(X0,X1),X2) != X2
          & r2_hidden(X2,u1_struct_0(X1))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_funct_1(k4_tmap_1(X0,X1),sK2) != sK2
        & r2_hidden(sK2,u1_struct_0(X1))
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) != X2
              & r2_hidden(X2,u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( k1_funct_1(k4_tmap_1(X0,sK1),X2) != X2
            & r2_hidden(X2,u1_struct_0(sK1))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_funct_1(k4_tmap_1(X0,X1),X2) != X2
                & r2_hidden(X2,u1_struct_0(X1))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k4_tmap_1(sK0,X1),X2) != X2
              & r2_hidden(X2,u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK2) != sK2
    & r2_hidden(sK2,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f35,f34,f33])).

fof(f57,plain,(
    r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_relat_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0] :
      ( v1_funct_1(k3_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X0] :
      ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => k2_tmap_1(X0,X0,k3_struct_0(X0),X1) = k4_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tmap_1(X0,X0,k3_struct_0(X0),X1) = k4_tmap_1(X0,X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tmap_1(X0,X0,k3_struct_0(X0),X1) = k4_tmap_1(X0,X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(X0,X0,k3_struct_0(X0),X1) = k4_tmap_1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    k1_funct_1(k4_tmap_1(sK0,sK1),sK2) != sK2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1145,negated_conjecture,
    ( r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1335,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1145])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_0,plain,
    ( ~ l1_struct_0(X0)
    | k6_relat_1(u1_struct_0(X0)) = k3_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_380,plain,
    ( ~ l1_pre_topc(X0)
    | k6_relat_1(u1_struct_0(X0)) = k3_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_0])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_693,plain,
    ( k6_relat_1(u1_struct_0(X0)) = k3_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_380,c_18])).

cnf(c_694,plain,
    ( k6_relat_1(u1_struct_0(sK0)) = k3_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_1141,plain,
    ( k6_relat_1(u1_struct_0(sK0)) = k3_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_694])).

cnf(c_5,plain,
    ( v1_funct_1(k3_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_347,plain,
    ( ~ l1_pre_topc(X0)
    | v1_funct_1(k3_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_7,c_5])).

cnf(c_705,plain,
    ( v1_funct_1(k3_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_347,c_18])).

cnf(c_706,plain,
    ( v1_funct_1(k3_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_705])).

cnf(c_6,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_234,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
    | k6_relat_1(X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_235,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_funct_1(k6_relat_1(X2))
    | k1_funct_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k1_funct_1(k6_relat_1(X2),X0) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_749,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k1_funct_1(k6_relat_1(X2),X0)
    | k6_relat_1(X2) != k3_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_706,c_235])).

cnf(c_1137,plain,
    ( ~ r2_hidden(X0_52,X0_53)
    | k1_funct_1(k7_relat_1(k6_relat_1(X1_53),X0_53),X0_52) = k1_funct_1(k6_relat_1(X1_53),X0_52)
    | k6_relat_1(X1_53) != k3_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_749])).

cnf(c_1341,plain,
    ( k1_funct_1(k7_relat_1(k6_relat_1(X0_53),X1_53),X0_52) = k1_funct_1(k6_relat_1(X0_53),X0_52)
    | k6_relat_1(X0_53) != k3_struct_0(sK0)
    | r2_hidden(X0_52,X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1137])).

cnf(c_1779,plain,
    ( k1_funct_1(k7_relat_1(k6_relat_1(u1_struct_0(sK0)),X0_53),X0_52) = k1_funct_1(k6_relat_1(u1_struct_0(sK0)),X0_52)
    | r2_hidden(X0_52,X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_1341])).

cnf(c_1780,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK0),X0_53),X0_52) = k1_funct_1(k3_struct_0(sK0),X0_52)
    | r2_hidden(X0_52,X0_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1779,c_1141])).

cnf(c_1787,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK2) = k1_funct_1(k3_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_1335,c_1780])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1144,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1336,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1144])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_333,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_7,c_8])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_593,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_333,c_20])).

cnf(c_594,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_41,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_44,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_596,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_594,c_20,c_18,c_41,c_44])).

cnf(c_609,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | u1_struct_0(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_596])).

cnf(c_610,plain,
    ( r2_hidden(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_1142,plain,
    ( r2_hidden(X0_52,u1_struct_0(sK0))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_610])).

cnf(c_1337,plain,
    ( r2_hidden(X0_52,u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1142])).

cnf(c_1617,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1336,c_1337])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1147,plain,
    ( ~ r2_hidden(X0_52,X0_53)
    | k1_funct_1(k6_relat_1(X0_53),X0_52) = X0_52 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1334,plain,
    ( k1_funct_1(k6_relat_1(X0_53),X0_52) = X0_52
    | r2_hidden(X0_52,X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1147])).

cnf(c_1621,plain,
    ( k1_funct_1(k6_relat_1(u1_struct_0(sK0)),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1617,c_1334])).

cnf(c_1622,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1621,c_1141])).

cnf(c_4,plain,
    ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_358,plain,
    ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_7,c_4])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_477,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | sK1 != X3
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_16])).

cnf(c_478,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK1)) = k2_tmap_1(sK0,X1,X0,sK1) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_482,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK1)) = k2_tmap_1(sK0,X1,X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_20,c_19,c_18])).

cnf(c_483,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK1)) = k2_tmap_1(sK0,X1,X0,sK1) ),
    inference(renaming,[status(thm)],[c_482])).

cnf(c_525,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK1)) = k2_tmap_1(sK0,X1,X0,sK1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_483,c_19])).

cnf(c_526,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),X0,u1_struct_0(sK1)) = k2_tmap_1(sK0,sK0,X0,sK1) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_530,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),X0,u1_struct_0(sK1)) = k2_tmap_1(sK0,sK0,X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_20,c_18])).

cnf(c_554,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),X0,u1_struct_0(sK1)) = k2_tmap_1(sK0,sK0,X0,sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | k3_struct_0(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_358,c_530])).

cnf(c_555,plain,
    ( ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(k3_struct_0(X0))
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(X0),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK0,k3_struct_0(X0),sK1)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_559,plain,
    ( ~ l1_pre_topc(X0)
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(X0),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK0,k3_struct_0(X0),sK1)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_555,c_347])).

cnf(c_560,plain,
    ( ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(X0),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK0,k3_struct_0(X0),sK1)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_559])).

cnf(c_682,plain,
    ( ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(X0),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK0,k3_struct_0(X0),sK1)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_560,c_18])).

cnf(c_683,plain,
    ( ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_3,plain,
    ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_56,plain,
    ( m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_562,plain,
    ( ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_685,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_683,c_18,c_44,c_56,c_562])).

cnf(c_937,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_685])).

cnf(c_1136,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) ),
    inference(subtyping,[status(esa)],[c_937])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,X1,k3_struct_0(X1),X0) = k4_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_508,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,X0,k3_struct_0(X0),X1) = k4_tmap_1(X0,X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_16])).

cnf(c_509,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = k4_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_511,plain,
    ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = k4_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_20,c_19,c_18])).

cnf(c_1143,plain,
    ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = k4_tmap_1(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_511])).

cnf(c_1362,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),u1_struct_0(sK1)) = k4_tmap_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1136,c_1143])).

cnf(c_369,plain,
    ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_7,c_3])).

cnf(c_698,plain,
    ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_369,c_18])).

cnf(c_699,plain,
    ( m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_698])).

cnf(c_1140,plain,
    ( m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_699])).

cnf(c_1338,plain,
    ( m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1140])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_737,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | k3_struct_0(sK0) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_706])).

cnf(c_738,plain,
    ( ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,k3_struct_0(sK0),X2) = k7_relat_1(k3_struct_0(sK0),X2) ),
    inference(unflattening,[status(thm)],[c_737])).

cnf(c_1138,plain,
    ( ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_partfun1(X0_53,X1_53,k3_struct_0(sK0),X2_53) = k7_relat_1(k3_struct_0(sK0),X2_53) ),
    inference(subtyping,[status(esa)],[c_738])).

cnf(c_1340,plain,
    ( k2_partfun1(X0_53,X1_53,k3_struct_0(sK0),X2_53) = k7_relat_1(k3_struct_0(sK0),X2_53)
    | m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_1664,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),X0_53) = k7_relat_1(k3_struct_0(sK0),X0_53) ),
    inference(superposition,[status(thm)],[c_1338,c_1340])).

cnf(c_1707,plain,
    ( k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)) = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1362,c_1664])).

cnf(c_1793,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1787,c_1622,c_1707])).

cnf(c_13,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK2) != sK2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1146,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK2) != sK2 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1793,c_1146])).


%------------------------------------------------------------------------------
