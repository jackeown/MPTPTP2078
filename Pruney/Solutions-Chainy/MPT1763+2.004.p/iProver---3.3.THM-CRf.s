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
% DateTime   : Thu Dec  3 12:22:52 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  216 (1669 expanded)
%              Number of clauses        :  149 ( 497 expanded)
%              Number of leaves         :   26 ( 490 expanded)
%              Depth                    :   20
%              Number of atoms          :  885 (11760 expanded)
%              Number of equality atoms :  327 ( 808 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X3) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),sK3,k3_tmap_1(X0,X1,X2,X2,sK3))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,sK2,sK2,X3))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X1))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),X3,k3_tmap_1(X0,sK1,X2,X2,X3))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(sK0,X1,X2,X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f43,f42,f41,f40])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_786,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1175,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_372,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_3,c_7])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_7,c_3,c_2])).

cnf(c_377,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_376])).

cnf(c_449,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_377])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_7,c_4,c_3,c_2])).

cnf(c_454,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_453])).

cnf(c_772,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | v1_xboole_0(X1_55)
    | ~ v1_funct_1(X0_54)
    | k1_relat_1(X0_54) = X0_55 ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_1190,plain,
    ( k1_relat_1(X0_54) = X0_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_1950,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1175,c_1190])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_47,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_50,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1365,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_794,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_1459,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_798,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_1527,plain,
    ( X0_55 != X1_55
    | u1_struct_0(sK2) != X1_55
    | u1_struct_0(sK2) = X0_55 ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_1612,plain,
    ( X0_55 != u1_struct_0(sK2)
    | u1_struct_0(sK2) = X0_55
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1527])).

cnf(c_1762,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = k1_relat_1(sK3)
    | k1_relat_1(sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1612])).

cnf(c_2011,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1950,c_23,c_21,c_18,c_17,c_16,c_47,c_50,c_1365,c_1459,c_1762])).

cnf(c_0,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_3,c_0])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_3,c_2,c_0])).

cnf(c_773,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k7_relat_1(X0_54,X0_55) = X0_54 ),
    inference(subtyping,[status(esa)],[c_396])).

cnf(c_1189,plain,
    ( k7_relat_1(X0_54,X0_55) = X0_54
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_1654,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_1175,c_1189])).

cnf(c_1,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,X0)
    | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_512,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_relat_1(X3)
    | u1_struct_0(X0) != X4
    | k1_relat_1(k7_relat_1(X3,X4)) != u1_struct_0(X2) ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_513,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_relat_1(X3)
    | k1_relat_1(k7_relat_1(X3,u1_struct_0(X2))) != u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_771,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_pre_topc(X2_53,X1_53)
    | m1_pre_topc(X0_53,X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v1_relat_1(X0_54)
    | k1_relat_1(k7_relat_1(X0_54,u1_struct_0(X2_53))) != u1_struct_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_513])).

cnf(c_1191,plain,
    ( k1_relat_1(k7_relat_1(X0_54,u1_struct_0(X0_53))) != u1_struct_0(X1_53)
    | m1_pre_topc(X1_53,X2_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) = iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_1782,plain,
    ( u1_struct_0(X0_53) != k1_relat_1(sK3)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK2) = iProver_top
    | m1_pre_topc(sK2,X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1654,c_1191])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_789,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1349,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_789])).

cnf(c_1350,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1349])).

cnf(c_1849,plain,
    ( l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | m1_pre_topc(sK2,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK2) = iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | u1_struct_0(X0_53) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1782,c_37,c_1350])).

cnf(c_1850,plain,
    ( u1_struct_0(X0_53) != k1_relat_1(sK3)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK2) = iProver_top
    | m1_pre_topc(sK2,X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_1849])).

cnf(c_2037,plain,
    ( m1_pre_topc(sK2,X0_53) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2011,c_1850])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_29,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_34,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1357,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k7_relat_1(sK3,u1_struct_0(sK2)) = sK3 ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_795,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_1396,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_1407,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_1421,plain,
    ( ~ m1_pre_topc(X0_53,sK0)
    | m1_pre_topc(sK2,X0_53)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_relat_1(X0_54)
    | k1_relat_1(k7_relat_1(X0_54,u1_struct_0(X0_53))) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_1426,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_relat_1(X0_54)
    | k1_relat_1(k7_relat_1(X0_54,u1_struct_0(sK2))) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1421])).

cnf(c_1427,plain,
    ( k1_relat_1(k7_relat_1(X0_54,u1_struct_0(sK2))) != u1_struct_0(sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1426])).

cnf(c_1429,plain,
    ( k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) != u1_struct_0(sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_1514,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(X0_54)
    | k1_relat_1(X0_54) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_1633,plain,
    ( ~ v1_funct_2(k7_relat_1(X0_54,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k7_relat_1(X0_54,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(X0_54,u1_struct_0(sK2)))
    | k1_relat_1(k7_relat_1(X0_54,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1514])).

cnf(c_1635,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_805,plain,
    ( ~ v1_funct_1(X0_54)
    | v1_funct_1(X1_54)
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_1711,plain,
    ( ~ v1_funct_1(X0_54)
    | v1_funct_1(k7_relat_1(X1_54,u1_struct_0(sK2)))
    | k7_relat_1(X1_54,u1_struct_0(sK2)) != X0_54 ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_1713,plain,
    ( v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ v1_funct_1(sK3)
    | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_1711])).

cnf(c_804,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | v1_funct_2(X1_54,X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_1377,plain,
    ( v1_funct_2(X0_54,X0_55,X1_55)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | X1_55 != u1_struct_0(sK1)
    | X0_55 != u1_struct_0(sK2)
    | X0_54 != sK3 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_1406,plain,
    ( v1_funct_2(X0_54,X0_55,u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | X0_55 != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | X0_54 != sK3 ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_1458,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | X0_54 != sK3 ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_1963,plain,
    ( v1_funct_2(k7_relat_1(X0_54,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | k7_relat_1(X0_54,u1_struct_0(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_1965,plain,
    ( v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_1963])).

cnf(c_803,plain,
    ( ~ m1_subset_1(X0_54,X0_56)
    | m1_subset_1(X1_54,X1_56)
    | X1_56 != X0_56
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_1360,plain,
    ( m1_subset_1(X0_54,X0_56)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | X0_56 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | X0_54 != sK3 ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1395,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | X0_54 != sK3 ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_2336,plain,
    ( m1_subset_1(k7_relat_1(X0_54,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | k7_relat_1(X0_54,u1_struct_0(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_1395])).

cnf(c_2338,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_2336])).

cnf(c_2391,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2037,c_28,c_29,c_23,c_21,c_34,c_18,c_17,c_16,c_37,c_47,c_50,c_1350,c_1357,c_1396,c_1407,c_1429,c_1459,c_1635,c_1713,c_1965,c_2338])).

cnf(c_783,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1178,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_787,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X0_53)
    | ~ m1_pre_topc(X2_53,X3_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X3_53)
    | v2_struct_0(X3_53)
    | v2_struct_0(X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X3_53)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1174,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_54)
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X2_53,X3_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_1800,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK2,X0_53,sK3)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1175,c_1174])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_788,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X0_55,X1_55,X0_54,X2_55) = k7_relat_1(X0_54,X2_55) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1173,plain,
    ( k2_partfun1(X0_55,X1_55,X0_54,X2_55) = k7_relat_1(X0_54,X2_55)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_1533,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_55) = k7_relat_1(sK3,X0_55)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1175,c_1173])).

cnf(c_1372,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_55) = k7_relat_1(sK3,X0_55) ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_1587,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_55) = k7_relat_1(sK3,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1533,c_18,c_16,c_1372])).

cnf(c_1801,plain,
    ( k3_tmap_1(X0_53,sK1,sK2,X1_53,sK3) = k7_relat_1(sK3,u1_struct_0(X1_53))
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X1_53,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1800,c_1587])).

cnf(c_30,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_32,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_36,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1862,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | k3_tmap_1(X0_53,sK1,sK2,X1_53,sK3) = k7_relat_1(sK3,u1_struct_0(X1_53))
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X1_53,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1801,c_30,c_31,c_32,c_35,c_36])).

cnf(c_1863,plain,
    ( k3_tmap_1(X0_53,sK1,sK2,X1_53,sK3) = k7_relat_1(sK3,u1_struct_0(X1_53))
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X1_53,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_1862])).

cnf(c_1875,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = k7_relat_1(sK3,u1_struct_0(sK2))
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1863])).

cnf(c_1876,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = sK3
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1875,c_1654])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_27,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1938,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1876,c_27,c_28,c_29,c_34])).

cnf(c_1939,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = sK3
    | m1_pre_topc(sK2,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1938])).

cnf(c_2397,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_2391,c_1939])).

cnf(c_9,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_15,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_337,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_338,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
    | sK3 != k3_tmap_1(sK0,sK1,sK2,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_774,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
    | sK3 != k3_tmap_1(sK0,sK1,sK2,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_338])).

cnf(c_791,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
    | sP0_iProver_split
    | sK3 != k3_tmap_1(sK0,sK1,sK2,sK2,sK3) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_774])).

cnf(c_1187,plain,
    ( sK3 != k3_tmap_1(sK0,sK1,sK2,sK2,sK3)
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_790,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_774])).

cnf(c_1188,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_1271,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != sK3
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1187,c_1188])).

cnf(c_1352,plain,
    ( ~ v1_funct_1(X0_54)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
    | k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != X0_54 ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_1353,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != X0_54
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1352])).

cnf(c_1355,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != sK3
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_1644,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1271,c_35,c_1355])).

cnf(c_1645,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != sK3
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1644])).

cnf(c_2015,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != sK3
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2011,c_1645])).

cnf(c_2413,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2015,c_27,c_28,c_29,c_23,c_21,c_34,c_18,c_17,c_16,c_37,c_47,c_50,c_1350,c_1357,c_1396,c_1407,c_1429,c_1459,c_1635,c_1713,c_1876,c_1965,c_2338])).

cnf(c_2711,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2397,c_2413])).

cnf(c_1442,plain,
    ( m1_subset_1(X0_54,X0_56)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | X0_56 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | X0_54 != X1_54 ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1968,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))))
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | X1_54 != X0_54 ),
    inference(instantiation,[status(thm)],[c_1442])).

cnf(c_1970,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | X0_54 != X1_54
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1968])).

cnf(c_1972,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1970])).

cnf(c_802,plain,
    ( X0_57 != X1_57
    | k1_zfmisc_1(X0_57) = k1_zfmisc_1(X1_57) ),
    theory(equality)).

cnf(c_1400,plain,
    ( X0_57 != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | k1_zfmisc_1(X0_57) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_1451,plain,
    ( k2_zfmisc_1(X0_55,X1_55) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_1581,plain,
    ( k2_zfmisc_1(X0_55,u1_struct_0(sK1)) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_1925,plain,
    ( k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1581])).

cnf(c_801,plain,
    ( k2_zfmisc_1(X0_55,X1_55) = k2_zfmisc_1(X2_55,X3_55)
    | X0_55 != X2_55
    | X1_55 != X3_55 ),
    theory(equality)).

cnf(c_1452,plain,
    ( k2_zfmisc_1(X0_55,X1_55) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | X1_55 != u1_struct_0(sK1)
    | X0_55 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1524,plain,
    ( k2_zfmisc_1(X0_55,u1_struct_0(sK1)) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | X0_55 != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1452])).

cnf(c_1757,plain,
    ( k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k1_relat_1(sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1524])).

cnf(c_1464,plain,
    ( v1_funct_2(X0_54,k1_relat_1(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k1_relat_1(sK3) != u1_struct_0(sK2)
    | X0_54 != sK3 ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_1465,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | k1_relat_1(sK3) != u1_struct_0(sK2)
    | X0_54 != sK3
    | v1_funct_2(X0_54,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1464])).

cnf(c_1467,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | k1_relat_1(sK3) != u1_struct_0(sK2)
    | sK3 != sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1465])).

cnf(c_793,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_820,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2711,c_1972,c_1925,c_1757,c_1467,c_1407,c_1365,c_820,c_50,c_47,c_37,c_16,c_36,c_17,c_18,c_21,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.70/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/0.98  
% 1.70/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.70/0.98  
% 1.70/0.98  ------  iProver source info
% 1.70/0.98  
% 1.70/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.70/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.70/0.98  git: non_committed_changes: false
% 1.70/0.98  git: last_make_outside_of_git: false
% 1.70/0.98  
% 1.70/0.98  ------ 
% 1.70/0.98  
% 1.70/0.98  ------ Input Options
% 1.70/0.98  
% 1.70/0.98  --out_options                           all
% 1.70/0.98  --tptp_safe_out                         true
% 1.70/0.98  --problem_path                          ""
% 1.70/0.98  --include_path                          ""
% 1.70/0.98  --clausifier                            res/vclausify_rel
% 1.70/0.98  --clausifier_options                    --mode clausify
% 1.70/0.98  --stdin                                 false
% 1.70/0.98  --stats_out                             all
% 1.70/0.98  
% 1.70/0.98  ------ General Options
% 1.70/0.98  
% 1.70/0.98  --fof                                   false
% 1.70/0.98  --time_out_real                         305.
% 1.70/0.98  --time_out_virtual                      -1.
% 1.70/0.98  --symbol_type_check                     false
% 1.70/0.98  --clausify_out                          false
% 1.70/0.98  --sig_cnt_out                           false
% 1.70/0.98  --trig_cnt_out                          false
% 1.70/0.98  --trig_cnt_out_tolerance                1.
% 1.70/0.98  --trig_cnt_out_sk_spl                   false
% 1.70/0.98  --abstr_cl_out                          false
% 1.70/0.98  
% 1.70/0.98  ------ Global Options
% 1.70/0.98  
% 1.70/0.98  --schedule                              default
% 1.70/0.98  --add_important_lit                     false
% 1.70/0.98  --prop_solver_per_cl                    1000
% 1.70/0.98  --min_unsat_core                        false
% 1.70/0.98  --soft_assumptions                      false
% 1.70/0.98  --soft_lemma_size                       3
% 1.70/0.98  --prop_impl_unit_size                   0
% 1.70/0.98  --prop_impl_unit                        []
% 1.70/0.98  --share_sel_clauses                     true
% 1.70/0.98  --reset_solvers                         false
% 1.70/0.98  --bc_imp_inh                            [conj_cone]
% 1.70/0.98  --conj_cone_tolerance                   3.
% 1.70/0.98  --extra_neg_conj                        none
% 1.70/0.98  --large_theory_mode                     true
% 1.70/0.98  --prolific_symb_bound                   200
% 1.70/0.98  --lt_threshold                          2000
% 1.70/0.98  --clause_weak_htbl                      true
% 1.70/0.98  --gc_record_bc_elim                     false
% 1.70/0.98  
% 1.70/0.98  ------ Preprocessing Options
% 1.70/0.98  
% 1.70/0.98  --preprocessing_flag                    true
% 1.70/0.98  --time_out_prep_mult                    0.1
% 1.70/0.98  --splitting_mode                        input
% 1.70/0.98  --splitting_grd                         true
% 1.70/0.98  --splitting_cvd                         false
% 1.70/0.98  --splitting_cvd_svl                     false
% 1.70/0.98  --splitting_nvd                         32
% 1.70/0.98  --sub_typing                            true
% 1.70/0.98  --prep_gs_sim                           true
% 1.70/0.98  --prep_unflatten                        true
% 1.70/0.98  --prep_res_sim                          true
% 1.70/0.98  --prep_upred                            true
% 1.70/0.98  --prep_sem_filter                       exhaustive
% 1.70/0.98  --prep_sem_filter_out                   false
% 1.70/0.98  --pred_elim                             true
% 1.70/0.98  --res_sim_input                         true
% 1.70/0.98  --eq_ax_congr_red                       true
% 1.70/0.98  --pure_diseq_elim                       true
% 1.70/0.98  --brand_transform                       false
% 1.70/0.98  --non_eq_to_eq                          false
% 1.70/0.98  --prep_def_merge                        true
% 1.70/0.98  --prep_def_merge_prop_impl              false
% 1.70/0.98  --prep_def_merge_mbd                    true
% 1.70/0.98  --prep_def_merge_tr_red                 false
% 1.70/0.98  --prep_def_merge_tr_cl                  false
% 1.70/0.98  --smt_preprocessing                     true
% 1.70/0.98  --smt_ac_axioms                         fast
% 1.70/0.98  --preprocessed_out                      false
% 1.70/0.98  --preprocessed_stats                    false
% 1.70/0.98  
% 1.70/0.98  ------ Abstraction refinement Options
% 1.70/0.98  
% 1.70/0.98  --abstr_ref                             []
% 1.70/0.98  --abstr_ref_prep                        false
% 1.70/0.98  --abstr_ref_until_sat                   false
% 1.70/0.98  --abstr_ref_sig_restrict                funpre
% 1.70/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.70/0.98  --abstr_ref_under                       []
% 1.70/0.98  
% 1.70/0.98  ------ SAT Options
% 1.70/0.98  
% 1.70/0.98  --sat_mode                              false
% 1.70/0.98  --sat_fm_restart_options                ""
% 1.70/0.98  --sat_gr_def                            false
% 1.70/0.98  --sat_epr_types                         true
% 1.70/0.98  --sat_non_cyclic_types                  false
% 1.70/0.98  --sat_finite_models                     false
% 1.70/0.98  --sat_fm_lemmas                         false
% 1.70/0.98  --sat_fm_prep                           false
% 1.70/0.98  --sat_fm_uc_incr                        true
% 1.70/0.98  --sat_out_model                         small
% 1.70/0.98  --sat_out_clauses                       false
% 1.70/0.98  
% 1.70/0.98  ------ QBF Options
% 1.70/0.98  
% 1.70/0.98  --qbf_mode                              false
% 1.70/0.98  --qbf_elim_univ                         false
% 1.70/0.98  --qbf_dom_inst                          none
% 1.70/0.98  --qbf_dom_pre_inst                      false
% 1.70/0.98  --qbf_sk_in                             false
% 1.70/0.98  --qbf_pred_elim                         true
% 1.70/0.98  --qbf_split                             512
% 1.70/0.98  
% 1.70/0.98  ------ BMC1 Options
% 1.70/0.98  
% 1.70/0.98  --bmc1_incremental                      false
% 1.70/0.98  --bmc1_axioms                           reachable_all
% 1.70/0.98  --bmc1_min_bound                        0
% 1.70/0.98  --bmc1_max_bound                        -1
% 1.70/0.98  --bmc1_max_bound_default                -1
% 1.70/0.98  --bmc1_symbol_reachability              true
% 1.70/0.98  --bmc1_property_lemmas                  false
% 1.70/0.98  --bmc1_k_induction                      false
% 1.70/0.98  --bmc1_non_equiv_states                 false
% 1.70/0.98  --bmc1_deadlock                         false
% 1.70/0.98  --bmc1_ucm                              false
% 1.70/0.98  --bmc1_add_unsat_core                   none
% 1.70/0.98  --bmc1_unsat_core_children              false
% 1.70/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.70/0.98  --bmc1_out_stat                         full
% 1.70/0.98  --bmc1_ground_init                      false
% 1.70/0.98  --bmc1_pre_inst_next_state              false
% 1.70/0.98  --bmc1_pre_inst_state                   false
% 1.70/0.98  --bmc1_pre_inst_reach_state             false
% 1.70/0.98  --bmc1_out_unsat_core                   false
% 1.70/0.98  --bmc1_aig_witness_out                  false
% 1.70/0.98  --bmc1_verbose                          false
% 1.70/0.98  --bmc1_dump_clauses_tptp                false
% 1.70/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.70/0.98  --bmc1_dump_file                        -
% 1.70/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.70/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.70/0.98  --bmc1_ucm_extend_mode                  1
% 1.70/0.98  --bmc1_ucm_init_mode                    2
% 1.70/0.98  --bmc1_ucm_cone_mode                    none
% 1.70/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.70/0.98  --bmc1_ucm_relax_model                  4
% 1.70/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.70/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.70/0.98  --bmc1_ucm_layered_model                none
% 1.70/0.98  --bmc1_ucm_max_lemma_size               10
% 1.70/0.98  
% 1.70/0.98  ------ AIG Options
% 1.70/0.98  
% 1.70/0.98  --aig_mode                              false
% 1.70/0.98  
% 1.70/0.98  ------ Instantiation Options
% 1.70/0.98  
% 1.70/0.98  --instantiation_flag                    true
% 1.70/0.98  --inst_sos_flag                         false
% 1.70/0.98  --inst_sos_phase                        true
% 1.70/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.70/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.70/0.98  --inst_lit_sel_side                     num_symb
% 1.70/0.98  --inst_solver_per_active                1400
% 1.70/0.98  --inst_solver_calls_frac                1.
% 1.70/0.98  --inst_passive_queue_type               priority_queues
% 1.70/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.70/0.98  --inst_passive_queues_freq              [25;2]
% 1.70/0.98  --inst_dismatching                      true
% 1.70/0.98  --inst_eager_unprocessed_to_passive     true
% 1.70/0.98  --inst_prop_sim_given                   true
% 1.70/0.98  --inst_prop_sim_new                     false
% 1.70/0.98  --inst_subs_new                         false
% 1.70/0.98  --inst_eq_res_simp                      false
% 1.70/0.98  --inst_subs_given                       false
% 1.70/0.98  --inst_orphan_elimination               true
% 1.70/0.98  --inst_learning_loop_flag               true
% 1.70/0.98  --inst_learning_start                   3000
% 1.70/0.98  --inst_learning_factor                  2
% 1.70/0.98  --inst_start_prop_sim_after_learn       3
% 1.70/0.98  --inst_sel_renew                        solver
% 1.70/0.98  --inst_lit_activity_flag                true
% 1.70/0.98  --inst_restr_to_given                   false
% 1.70/0.98  --inst_activity_threshold               500
% 1.70/0.98  --inst_out_proof                        true
% 1.70/0.98  
% 1.70/0.98  ------ Resolution Options
% 1.70/0.98  
% 1.70/0.98  --resolution_flag                       true
% 1.70/0.98  --res_lit_sel                           adaptive
% 1.70/0.98  --res_lit_sel_side                      none
% 1.70/0.98  --res_ordering                          kbo
% 1.70/0.98  --res_to_prop_solver                    active
% 1.70/0.98  --res_prop_simpl_new                    false
% 1.70/0.98  --res_prop_simpl_given                  true
% 1.70/0.98  --res_passive_queue_type                priority_queues
% 1.70/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.70/0.98  --res_passive_queues_freq               [15;5]
% 1.70/0.98  --res_forward_subs                      full
% 1.70/0.98  --res_backward_subs                     full
% 1.70/0.98  --res_forward_subs_resolution           true
% 1.70/0.98  --res_backward_subs_resolution          true
% 1.70/0.98  --res_orphan_elimination                true
% 1.70/0.98  --res_time_limit                        2.
% 1.70/0.98  --res_out_proof                         true
% 1.70/0.98  
% 1.70/0.98  ------ Superposition Options
% 1.70/0.98  
% 1.70/0.98  --superposition_flag                    true
% 1.70/0.98  --sup_passive_queue_type                priority_queues
% 1.70/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.70/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.70/0.98  --demod_completeness_check              fast
% 1.70/0.98  --demod_use_ground                      true
% 1.70/0.98  --sup_to_prop_solver                    passive
% 1.70/0.98  --sup_prop_simpl_new                    true
% 1.70/0.98  --sup_prop_simpl_given                  true
% 1.70/0.98  --sup_fun_splitting                     false
% 1.70/0.98  --sup_smt_interval                      50000
% 1.70/0.98  
% 1.70/0.98  ------ Superposition Simplification Setup
% 1.70/0.98  
% 1.70/0.98  --sup_indices_passive                   []
% 1.70/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.70/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.98  --sup_full_bw                           [BwDemod]
% 1.70/0.98  --sup_immed_triv                        [TrivRules]
% 1.70/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.70/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.98  --sup_immed_bw_main                     []
% 1.70/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.70/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.98  
% 1.70/0.98  ------ Combination Options
% 1.70/0.98  
% 1.70/0.98  --comb_res_mult                         3
% 1.70/0.98  --comb_sup_mult                         2
% 1.70/0.98  --comb_inst_mult                        10
% 1.70/0.98  
% 1.70/0.98  ------ Debug Options
% 1.70/0.98  
% 1.70/0.98  --dbg_backtrace                         false
% 1.70/0.98  --dbg_dump_prop_clauses                 false
% 1.70/0.98  --dbg_dump_prop_clauses_file            -
% 1.70/0.98  --dbg_out_stat                          false
% 1.70/0.98  ------ Parsing...
% 1.70/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.70/0.98  
% 1.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.70/0.98  
% 1.70/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.70/0.98  
% 1.70/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.70/0.98  ------ Proving...
% 1.70/0.98  ------ Problem Properties 
% 1.70/0.98  
% 1.70/0.98  
% 1.70/0.98  clauses                                 20
% 1.70/0.98  conjectures                             11
% 1.70/0.98  EPR                                     9
% 1.70/0.98  Horn                                    18
% 1.70/0.98  unary                                   11
% 1.70/0.98  binary                                  2
% 1.70/0.98  lits                                    55
% 1.70/0.98  lits eq                                 6
% 1.70/0.98  fd_pure                                 0
% 1.70/0.98  fd_pseudo                               0
% 1.70/0.98  fd_cond                                 0
% 1.70/0.98  fd_pseudo_cond                          1
% 1.70/0.98  AC symbols                              0
% 1.70/0.98  
% 1.70/0.98  ------ Schedule dynamic 5 is on 
% 1.70/0.98  
% 1.70/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.70/0.98  
% 1.70/0.98  
% 1.70/0.98  ------ 
% 1.70/0.98  Current options:
% 1.70/0.98  ------ 
% 1.70/0.98  
% 1.70/0.98  ------ Input Options
% 1.70/0.98  
% 1.70/0.98  --out_options                           all
% 1.70/0.98  --tptp_safe_out                         true
% 1.70/0.98  --problem_path                          ""
% 1.70/0.98  --include_path                          ""
% 1.70/0.98  --clausifier                            res/vclausify_rel
% 1.70/0.98  --clausifier_options                    --mode clausify
% 1.70/0.98  --stdin                                 false
% 1.70/0.98  --stats_out                             all
% 1.70/0.98  
% 1.70/0.98  ------ General Options
% 1.70/0.98  
% 1.70/0.98  --fof                                   false
% 1.70/0.98  --time_out_real                         305.
% 1.70/0.98  --time_out_virtual                      -1.
% 1.70/0.98  --symbol_type_check                     false
% 1.70/0.98  --clausify_out                          false
% 1.70/0.98  --sig_cnt_out                           false
% 1.70/0.98  --trig_cnt_out                          false
% 1.70/0.98  --trig_cnt_out_tolerance                1.
% 1.70/0.98  --trig_cnt_out_sk_spl                   false
% 1.70/0.98  --abstr_cl_out                          false
% 1.70/0.98  
% 1.70/0.98  ------ Global Options
% 1.70/0.98  
% 1.70/0.98  --schedule                              default
% 1.70/0.98  --add_important_lit                     false
% 1.70/0.98  --prop_solver_per_cl                    1000
% 1.70/0.98  --min_unsat_core                        false
% 1.70/0.98  --soft_assumptions                      false
% 1.70/0.98  --soft_lemma_size                       3
% 1.70/0.98  --prop_impl_unit_size                   0
% 1.70/0.98  --prop_impl_unit                        []
% 1.70/0.98  --share_sel_clauses                     true
% 1.70/0.98  --reset_solvers                         false
% 1.70/0.98  --bc_imp_inh                            [conj_cone]
% 1.70/0.98  --conj_cone_tolerance                   3.
% 1.70/0.98  --extra_neg_conj                        none
% 1.70/0.98  --large_theory_mode                     true
% 1.70/0.98  --prolific_symb_bound                   200
% 1.70/0.98  --lt_threshold                          2000
% 1.70/0.98  --clause_weak_htbl                      true
% 1.70/0.98  --gc_record_bc_elim                     false
% 1.70/0.98  
% 1.70/0.98  ------ Preprocessing Options
% 1.70/0.98  
% 1.70/0.98  --preprocessing_flag                    true
% 1.70/0.98  --time_out_prep_mult                    0.1
% 1.70/0.98  --splitting_mode                        input
% 1.70/0.98  --splitting_grd                         true
% 1.70/0.98  --splitting_cvd                         false
% 1.70/0.98  --splitting_cvd_svl                     false
% 1.70/0.98  --splitting_nvd                         32
% 1.70/0.98  --sub_typing                            true
% 1.70/0.98  --prep_gs_sim                           true
% 1.70/0.98  --prep_unflatten                        true
% 1.70/0.98  --prep_res_sim                          true
% 1.70/0.98  --prep_upred                            true
% 1.70/0.98  --prep_sem_filter                       exhaustive
% 1.70/0.98  --prep_sem_filter_out                   false
% 1.70/0.98  --pred_elim                             true
% 1.70/0.98  --res_sim_input                         true
% 1.70/0.98  --eq_ax_congr_red                       true
% 1.70/0.98  --pure_diseq_elim                       true
% 1.70/0.98  --brand_transform                       false
% 1.70/0.98  --non_eq_to_eq                          false
% 1.70/0.98  --prep_def_merge                        true
% 1.70/0.98  --prep_def_merge_prop_impl              false
% 1.70/0.98  --prep_def_merge_mbd                    true
% 1.70/0.98  --prep_def_merge_tr_red                 false
% 1.70/0.98  --prep_def_merge_tr_cl                  false
% 1.70/0.98  --smt_preprocessing                     true
% 1.70/0.98  --smt_ac_axioms                         fast
% 1.70/0.98  --preprocessed_out                      false
% 1.70/0.98  --preprocessed_stats                    false
% 1.70/0.98  
% 1.70/0.98  ------ Abstraction refinement Options
% 1.70/0.98  
% 1.70/0.98  --abstr_ref                             []
% 1.70/0.98  --abstr_ref_prep                        false
% 1.70/0.98  --abstr_ref_until_sat                   false
% 1.70/0.98  --abstr_ref_sig_restrict                funpre
% 1.70/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.70/0.98  --abstr_ref_under                       []
% 1.70/0.98  
% 1.70/0.98  ------ SAT Options
% 1.70/0.98  
% 1.70/0.98  --sat_mode                              false
% 1.70/0.98  --sat_fm_restart_options                ""
% 1.70/0.98  --sat_gr_def                            false
% 1.70/0.98  --sat_epr_types                         true
% 1.70/0.98  --sat_non_cyclic_types                  false
% 1.70/0.98  --sat_finite_models                     false
% 1.70/0.98  --sat_fm_lemmas                         false
% 1.70/0.98  --sat_fm_prep                           false
% 1.70/0.98  --sat_fm_uc_incr                        true
% 1.70/0.98  --sat_out_model                         small
% 1.70/0.98  --sat_out_clauses                       false
% 1.70/0.98  
% 1.70/0.98  ------ QBF Options
% 1.70/0.98  
% 1.70/0.98  --qbf_mode                              false
% 1.70/0.98  --qbf_elim_univ                         false
% 1.70/0.98  --qbf_dom_inst                          none
% 1.70/0.98  --qbf_dom_pre_inst                      false
% 1.70/0.98  --qbf_sk_in                             false
% 1.70/0.98  --qbf_pred_elim                         true
% 1.70/0.98  --qbf_split                             512
% 1.70/0.98  
% 1.70/0.98  ------ BMC1 Options
% 1.70/0.98  
% 1.70/0.98  --bmc1_incremental                      false
% 1.70/0.98  --bmc1_axioms                           reachable_all
% 1.70/0.98  --bmc1_min_bound                        0
% 1.70/0.98  --bmc1_max_bound                        -1
% 1.70/0.98  --bmc1_max_bound_default                -1
% 1.70/0.98  --bmc1_symbol_reachability              true
% 1.70/0.98  --bmc1_property_lemmas                  false
% 1.70/0.98  --bmc1_k_induction                      false
% 1.70/0.98  --bmc1_non_equiv_states                 false
% 1.70/0.98  --bmc1_deadlock                         false
% 1.70/0.98  --bmc1_ucm                              false
% 1.70/0.98  --bmc1_add_unsat_core                   none
% 1.70/0.98  --bmc1_unsat_core_children              false
% 1.70/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.70/0.98  --bmc1_out_stat                         full
% 1.70/0.98  --bmc1_ground_init                      false
% 1.70/0.98  --bmc1_pre_inst_next_state              false
% 1.70/0.98  --bmc1_pre_inst_state                   false
% 1.70/0.98  --bmc1_pre_inst_reach_state             false
% 1.70/0.98  --bmc1_out_unsat_core                   false
% 1.70/0.98  --bmc1_aig_witness_out                  false
% 1.70/0.98  --bmc1_verbose                          false
% 1.70/0.98  --bmc1_dump_clauses_tptp                false
% 1.70/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.70/0.98  --bmc1_dump_file                        -
% 1.70/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.70/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.70/0.98  --bmc1_ucm_extend_mode                  1
% 1.70/0.98  --bmc1_ucm_init_mode                    2
% 1.70/0.98  --bmc1_ucm_cone_mode                    none
% 1.70/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.70/0.98  --bmc1_ucm_relax_model                  4
% 1.70/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.70/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.70/0.98  --bmc1_ucm_layered_model                none
% 1.70/0.98  --bmc1_ucm_max_lemma_size               10
% 1.70/0.98  
% 1.70/0.98  ------ AIG Options
% 1.70/0.98  
% 1.70/0.98  --aig_mode                              false
% 1.70/0.98  
% 1.70/0.98  ------ Instantiation Options
% 1.70/0.98  
% 1.70/0.98  --instantiation_flag                    true
% 1.70/0.98  --inst_sos_flag                         false
% 1.70/0.98  --inst_sos_phase                        true
% 1.70/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.70/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.70/0.98  --inst_lit_sel_side                     none
% 1.70/0.98  --inst_solver_per_active                1400
% 1.70/0.98  --inst_solver_calls_frac                1.
% 1.70/0.98  --inst_passive_queue_type               priority_queues
% 1.70/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.70/0.98  --inst_passive_queues_freq              [25;2]
% 1.70/0.98  --inst_dismatching                      true
% 1.70/0.98  --inst_eager_unprocessed_to_passive     true
% 1.70/0.98  --inst_prop_sim_given                   true
% 1.70/0.98  --inst_prop_sim_new                     false
% 1.70/0.98  --inst_subs_new                         false
% 1.70/0.98  --inst_eq_res_simp                      false
% 1.70/0.98  --inst_subs_given                       false
% 1.70/0.98  --inst_orphan_elimination               true
% 1.70/0.98  --inst_learning_loop_flag               true
% 1.70/0.98  --inst_learning_start                   3000
% 1.70/0.98  --inst_learning_factor                  2
% 1.70/0.98  --inst_start_prop_sim_after_learn       3
% 1.70/0.98  --inst_sel_renew                        solver
% 1.70/0.98  --inst_lit_activity_flag                true
% 1.70/0.98  --inst_restr_to_given                   false
% 1.70/0.98  --inst_activity_threshold               500
% 1.70/0.98  --inst_out_proof                        true
% 1.70/0.98  
% 1.70/0.98  ------ Resolution Options
% 1.70/0.98  
% 1.70/0.98  --resolution_flag                       false
% 1.70/0.98  --res_lit_sel                           adaptive
% 1.70/0.98  --res_lit_sel_side                      none
% 1.70/0.98  --res_ordering                          kbo
% 1.70/0.98  --res_to_prop_solver                    active
% 1.70/0.98  --res_prop_simpl_new                    false
% 1.70/0.98  --res_prop_simpl_given                  true
% 1.70/0.98  --res_passive_queue_type                priority_queues
% 1.70/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.70/0.98  --res_passive_queues_freq               [15;5]
% 1.70/0.98  --res_forward_subs                      full
% 1.70/0.98  --res_backward_subs                     full
% 1.70/0.98  --res_forward_subs_resolution           true
% 1.70/0.98  --res_backward_subs_resolution          true
% 1.70/0.98  --res_orphan_elimination                true
% 1.70/0.98  --res_time_limit                        2.
% 1.70/0.98  --res_out_proof                         true
% 1.70/0.98  
% 1.70/0.98  ------ Superposition Options
% 1.70/0.98  
% 1.70/0.98  --superposition_flag                    true
% 1.70/0.98  --sup_passive_queue_type                priority_queues
% 1.70/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.70/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.70/0.98  --demod_completeness_check              fast
% 1.70/0.98  --demod_use_ground                      true
% 1.70/0.98  --sup_to_prop_solver                    passive
% 1.70/0.98  --sup_prop_simpl_new                    true
% 1.70/0.98  --sup_prop_simpl_given                  true
% 1.70/0.98  --sup_fun_splitting                     false
% 1.70/0.98  --sup_smt_interval                      50000
% 1.70/0.98  
% 1.70/0.98  ------ Superposition Simplification Setup
% 1.70/0.98  
% 1.70/0.98  --sup_indices_passive                   []
% 1.70/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.70/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.98  --sup_full_bw                           [BwDemod]
% 1.70/0.98  --sup_immed_triv                        [TrivRules]
% 1.70/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.70/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.98  --sup_immed_bw_main                     []
% 1.70/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.70/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.98  
% 1.70/0.98  ------ Combination Options
% 1.70/0.98  
% 1.70/0.98  --comb_res_mult                         3
% 1.70/0.98  --comb_sup_mult                         2
% 1.70/0.98  --comb_inst_mult                        10
% 1.70/0.98  
% 1.70/0.98  ------ Debug Options
% 1.70/0.98  
% 1.70/0.98  --dbg_backtrace                         false
% 1.70/0.98  --dbg_dump_prop_clauses                 false
% 1.70/0.98  --dbg_dump_prop_clauses_file            -
% 1.70/0.98  --dbg_out_stat                          false
% 1.70/0.98  
% 1.70/0.98  
% 1.70/0.98  
% 1.70/0.98  
% 1.70/0.98  ------ Proving...
% 1.70/0.98  
% 1.70/0.98  
% 1.70/0.98  % SZS status Theorem for theBenchmark.p
% 1.70/0.98  
% 1.70/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.70/0.98  
% 1.70/0.98  fof(f13,conjecture,(
% 1.70/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f14,negated_conjecture,(
% 1.70/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 1.70/0.98    inference(negated_conjecture,[],[f13])).
% 1.70/0.98  
% 1.70/0.98  fof(f36,plain,(
% 1.70/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.70/0.98    inference(ennf_transformation,[],[f14])).
% 1.70/0.98  
% 1.70/0.98  fof(f37,plain,(
% 1.70/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.70/0.98    inference(flattening,[],[f36])).
% 1.70/0.98  
% 1.70/0.98  fof(f43,plain,(
% 1.70/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),sK3,k3_tmap_1(X0,X1,X2,X2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 1.70/0.98    introduced(choice_axiom,[])).
% 1.70/0.98  
% 1.70/0.98  fof(f42,plain,(
% 1.70/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,sK2,sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 1.70/0.98    introduced(choice_axiom,[])).
% 1.70/0.98  
% 1.70/0.98  fof(f41,plain,(
% 1.70/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),X3,k3_tmap_1(X0,sK1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.70/0.98    introduced(choice_axiom,[])).
% 1.70/0.98  
% 1.70/0.98  fof(f40,plain,(
% 1.70/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(sK0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.70/0.98    introduced(choice_axiom,[])).
% 1.70/0.98  
% 1.70/0.98  fof(f44,plain,(
% 1.70/0.98    (((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.70/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f43,f42,f41,f40])).
% 1.70/0.98  
% 1.70/0.98  fof(f70,plain,(
% 1.70/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.70/0.98    inference(cnf_transformation,[],[f44])).
% 1.70/0.98  
% 1.70/0.98  fof(f5,axiom,(
% 1.70/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f21,plain,(
% 1.70/0.98    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.70/0.98    inference(ennf_transformation,[],[f5])).
% 1.70/0.98  
% 1.70/0.98  fof(f22,plain,(
% 1.70/0.98    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.70/0.98    inference(flattening,[],[f21])).
% 1.70/0.98  
% 1.70/0.98  fof(f50,plain,(
% 1.70/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f22])).
% 1.70/0.98  
% 1.70/0.98  fof(f4,axiom,(
% 1.70/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f15,plain,(
% 1.70/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.70/0.98    inference(pure_predicate_removal,[],[f4])).
% 1.70/0.98  
% 1.70/0.98  fof(f20,plain,(
% 1.70/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.98    inference(ennf_transformation,[],[f15])).
% 1.70/0.98  
% 1.70/0.98  fof(f48,plain,(
% 1.70/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.70/0.98    inference(cnf_transformation,[],[f20])).
% 1.70/0.98  
% 1.70/0.98  fof(f6,axiom,(
% 1.70/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f23,plain,(
% 1.70/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.70/0.98    inference(ennf_transformation,[],[f6])).
% 1.70/0.98  
% 1.70/0.98  fof(f24,plain,(
% 1.70/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.70/0.98    inference(flattening,[],[f23])).
% 1.70/0.98  
% 1.70/0.98  fof(f38,plain,(
% 1.70/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.70/0.98    inference(nnf_transformation,[],[f24])).
% 1.70/0.98  
% 1.70/0.98  fof(f51,plain,(
% 1.70/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f38])).
% 1.70/0.98  
% 1.70/0.98  fof(f3,axiom,(
% 1.70/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f19,plain,(
% 1.70/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.98    inference(ennf_transformation,[],[f3])).
% 1.70/0.98  
% 1.70/0.98  fof(f47,plain,(
% 1.70/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.70/0.98    inference(cnf_transformation,[],[f19])).
% 1.70/0.98  
% 1.70/0.98  fof(f63,plain,(
% 1.70/0.98    ~v2_struct_0(sK1)),
% 1.70/0.98    inference(cnf_transformation,[],[f44])).
% 1.70/0.98  
% 1.70/0.98  fof(f65,plain,(
% 1.70/0.98    l1_pre_topc(sK1)),
% 1.70/0.98    inference(cnf_transformation,[],[f44])).
% 1.70/0.98  
% 1.70/0.98  fof(f68,plain,(
% 1.70/0.98    v1_funct_1(sK3)),
% 1.70/0.98    inference(cnf_transformation,[],[f44])).
% 1.70/0.98  
% 1.70/0.98  fof(f69,plain,(
% 1.70/0.98    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.70/0.98    inference(cnf_transformation,[],[f44])).
% 1.70/0.98  
% 1.70/0.98  fof(f10,axiom,(
% 1.70/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f30,plain,(
% 1.70/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.70/0.98    inference(ennf_transformation,[],[f10])).
% 1.70/0.98  
% 1.70/0.98  fof(f31,plain,(
% 1.70/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.70/0.98    inference(flattening,[],[f30])).
% 1.70/0.98  
% 1.70/0.98  fof(f56,plain,(
% 1.70/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f31])).
% 1.70/0.98  
% 1.70/0.98  fof(f9,axiom,(
% 1.70/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f29,plain,(
% 1.70/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.70/0.98    inference(ennf_transformation,[],[f9])).
% 1.70/0.98  
% 1.70/0.98  fof(f55,plain,(
% 1.70/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f29])).
% 1.70/0.98  
% 1.70/0.98  fof(f1,axiom,(
% 1.70/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f16,plain,(
% 1.70/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.70/0.98    inference(ennf_transformation,[],[f1])).
% 1.70/0.98  
% 1.70/0.98  fof(f17,plain,(
% 1.70/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.70/0.98    inference(flattening,[],[f16])).
% 1.70/0.98  
% 1.70/0.98  fof(f45,plain,(
% 1.70/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f17])).
% 1.70/0.98  
% 1.70/0.98  fof(f2,axiom,(
% 1.70/0.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f18,plain,(
% 1.70/0.98    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.70/0.98    inference(ennf_transformation,[],[f2])).
% 1.70/0.98  
% 1.70/0.98  fof(f46,plain,(
% 1.70/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f18])).
% 1.70/0.98  
% 1.70/0.98  fof(f12,axiom,(
% 1.70/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f34,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.70/0.98    inference(ennf_transformation,[],[f12])).
% 1.70/0.98  
% 1.70/0.98  fof(f35,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.70/0.98    inference(flattening,[],[f34])).
% 1.70/0.98  
% 1.70/0.98  fof(f39,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.70/0.98    inference(nnf_transformation,[],[f35])).
% 1.70/0.98  
% 1.70/0.98  fof(f58,plain,(
% 1.70/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f39])).
% 1.70/0.98  
% 1.70/0.98  fof(f61,plain,(
% 1.70/0.98    v2_pre_topc(sK0)),
% 1.70/0.98    inference(cnf_transformation,[],[f44])).
% 1.70/0.98  
% 1.70/0.98  fof(f62,plain,(
% 1.70/0.98    l1_pre_topc(sK0)),
% 1.70/0.98    inference(cnf_transformation,[],[f44])).
% 1.70/0.98  
% 1.70/0.98  fof(f67,plain,(
% 1.70/0.98    m1_pre_topc(sK2,sK0)),
% 1.70/0.98    inference(cnf_transformation,[],[f44])).
% 1.70/0.98  
% 1.70/0.98  fof(f11,axiom,(
% 1.70/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f32,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.98    inference(ennf_transformation,[],[f11])).
% 1.70/0.98  
% 1.70/0.98  fof(f33,plain,(
% 1.70/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.98    inference(flattening,[],[f32])).
% 1.70/0.98  
% 1.70/0.98  fof(f57,plain,(
% 1.70/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f33])).
% 1.70/0.98  
% 1.70/0.98  fof(f7,axiom,(
% 1.70/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f25,plain,(
% 1.70/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.70/0.98    inference(ennf_transformation,[],[f7])).
% 1.70/0.98  
% 1.70/0.98  fof(f26,plain,(
% 1.70/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.70/0.98    inference(flattening,[],[f25])).
% 1.70/0.98  
% 1.70/0.98  fof(f53,plain,(
% 1.70/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f26])).
% 1.70/0.98  
% 1.70/0.98  fof(f64,plain,(
% 1.70/0.98    v2_pre_topc(sK1)),
% 1.70/0.98    inference(cnf_transformation,[],[f44])).
% 1.70/0.98  
% 1.70/0.98  fof(f60,plain,(
% 1.70/0.98    ~v2_struct_0(sK0)),
% 1.70/0.98    inference(cnf_transformation,[],[f44])).
% 1.70/0.98  
% 1.70/0.98  fof(f8,axiom,(
% 1.70/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 1.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.70/0.98  
% 1.70/0.98  fof(f27,plain,(
% 1.70/0.98    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.70/0.98    inference(ennf_transformation,[],[f8])).
% 1.70/0.98  
% 1.70/0.98  fof(f28,plain,(
% 1.70/0.98    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.70/0.98    inference(flattening,[],[f27])).
% 1.70/0.98  
% 1.70/0.98  fof(f54,plain,(
% 1.70/0.98    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.70/0.98    inference(cnf_transformation,[],[f28])).
% 1.70/0.98  
% 1.70/0.98  fof(f71,plain,(
% 1.70/0.98    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))),
% 1.70/0.98    inference(cnf_transformation,[],[f44])).
% 1.70/0.98  
% 1.70/0.98  cnf(c_16,negated_conjecture,
% 1.70/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 1.70/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_786,negated_conjecture,
% 1.70/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 1.70/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1175,plain,
% 1.70/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 1.70/0.98      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_4,plain,
% 1.70/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.70/0.98      | v1_partfun1(X0,X1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.98      | v1_xboole_0(X2)
% 1.70/0.98      | ~ v1_funct_1(X0) ),
% 1.70/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_3,plain,
% 1.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.98      | v4_relat_1(X0,X1) ),
% 1.70/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_7,plain,
% 1.70/0.98      ( ~ v1_partfun1(X0,X1)
% 1.70/0.98      | ~ v4_relat_1(X0,X1)
% 1.70/0.98      | ~ v1_relat_1(X0)
% 1.70/0.98      | k1_relat_1(X0) = X1 ),
% 1.70/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_372,plain,
% 1.70/0.98      ( ~ v1_partfun1(X0,X1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.98      | ~ v1_relat_1(X0)
% 1.70/0.98      | k1_relat_1(X0) = X1 ),
% 1.70/0.98      inference(resolution,[status(thm)],[c_3,c_7]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_2,plain,
% 1.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.98      | v1_relat_1(X0) ),
% 1.70/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_376,plain,
% 1.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.98      | ~ v1_partfun1(X0,X1)
% 1.70/0.98      | k1_relat_1(X0) = X1 ),
% 1.70/0.98      inference(global_propositional_subsumption,
% 1.70/0.98                [status(thm)],
% 1.70/0.98                [c_372,c_7,c_3,c_2]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_377,plain,
% 1.70/0.98      ( ~ v1_partfun1(X0,X1)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.98      | k1_relat_1(X0) = X1 ),
% 1.70/0.98      inference(renaming,[status(thm)],[c_376]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_449,plain,
% 1.70/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.70/0.98      | v1_xboole_0(X2)
% 1.70/0.98      | ~ v1_funct_1(X0)
% 1.70/0.98      | k1_relat_1(X0) = X1 ),
% 1.70/0.98      inference(resolution,[status(thm)],[c_4,c_377]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_453,plain,
% 1.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.98      | ~ v1_funct_2(X0,X1,X2)
% 1.70/0.98      | v1_xboole_0(X2)
% 1.70/0.98      | ~ v1_funct_1(X0)
% 1.70/0.98      | k1_relat_1(X0) = X1 ),
% 1.70/0.98      inference(global_propositional_subsumption,
% 1.70/0.98                [status(thm)],
% 1.70/0.98                [c_449,c_7,c_4,c_3,c_2]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_454,plain,
% 1.70/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.98      | v1_xboole_0(X2)
% 1.70/0.98      | ~ v1_funct_1(X0)
% 1.70/0.98      | k1_relat_1(X0) = X1 ),
% 1.70/0.98      inference(renaming,[status(thm)],[c_453]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_772,plain,
% 1.70/0.98      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 1.70/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 1.70/0.98      | v1_xboole_0(X1_55)
% 1.70/0.98      | ~ v1_funct_1(X0_54)
% 1.70/0.98      | k1_relat_1(X0_54) = X0_55 ),
% 1.70/0.98      inference(subtyping,[status(esa)],[c_454]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1190,plain,
% 1.70/0.98      ( k1_relat_1(X0_54) = X0_55
% 1.70/0.98      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 1.70/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 1.70/0.98      | v1_xboole_0(X1_55) = iProver_top
% 1.70/0.98      | v1_funct_1(X0_54) != iProver_top ),
% 1.70/0.98      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1950,plain,
% 1.70/0.98      ( u1_struct_0(sK2) = k1_relat_1(sK3)
% 1.70/0.98      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 1.70/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
% 1.70/0.98      | v1_funct_1(sK3) != iProver_top ),
% 1.70/0.98      inference(superposition,[status(thm)],[c_1175,c_1190]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_23,negated_conjecture,
% 1.70/0.98      ( ~ v2_struct_0(sK1) ),
% 1.70/0.98      inference(cnf_transformation,[],[f63]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_21,negated_conjecture,
% 1.70/0.98      ( l1_pre_topc(sK1) ),
% 1.70/0.98      inference(cnf_transformation,[],[f65]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_18,negated_conjecture,
% 1.70/0.98      ( v1_funct_1(sK3) ),
% 1.70/0.98      inference(cnf_transformation,[],[f68]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_17,negated_conjecture,
% 1.70/0.98      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 1.70/0.98      inference(cnf_transformation,[],[f69]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_11,plain,
% 1.70/0.98      ( v2_struct_0(X0)
% 1.70/0.98      | ~ l1_struct_0(X0)
% 1.70/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.70/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_47,plain,
% 1.70/0.98      ( v2_struct_0(sK1)
% 1.70/0.98      | ~ l1_struct_0(sK1)
% 1.70/0.98      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.70/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_10,plain,
% 1.70/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.70/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_50,plain,
% 1.70/0.98      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 1.70/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_1365,plain,
% 1.70/0.98      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.98      | v1_xboole_0(u1_struct_0(sK1))
% 1.70/0.98      | ~ v1_funct_1(sK3)
% 1.70/0.98      | k1_relat_1(sK3) = u1_struct_0(sK2) ),
% 1.70/0.98      inference(instantiation,[status(thm)],[c_772]) ).
% 1.70/0.98  
% 1.70/0.98  cnf(c_794,plain,( X0_55 = X0_55 ),theory(equality) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1459,plain,
% 1.70/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_794]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_798,plain,
% 1.70/0.99      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 1.70/0.99      theory(equality) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1527,plain,
% 1.70/0.99      ( X0_55 != X1_55
% 1.70/0.99      | u1_struct_0(sK2) != X1_55
% 1.70/0.99      | u1_struct_0(sK2) = X0_55 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_798]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1612,plain,
% 1.70/0.99      ( X0_55 != u1_struct_0(sK2)
% 1.70/0.99      | u1_struct_0(sK2) = X0_55
% 1.70/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1527]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1762,plain,
% 1.70/0.99      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.70/0.99      | u1_struct_0(sK2) = k1_relat_1(sK3)
% 1.70/0.99      | k1_relat_1(sK3) != u1_struct_0(sK2) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1612]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2011,plain,
% 1.70/0.99      ( u1_struct_0(sK2) = k1_relat_1(sK3) ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_1950,c_23,c_21,c_18,c_17,c_16,c_47,c_50,c_1365,c_1459,
% 1.70/0.99                 c_1762]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_0,plain,
% 1.70/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 1.70/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_392,plain,
% 1.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.99      | ~ v1_relat_1(X0)
% 1.70/0.99      | k7_relat_1(X0,X1) = X0 ),
% 1.70/0.99      inference(resolution,[status(thm)],[c_3,c_0]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_396,plain,
% 1.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.99      | k7_relat_1(X0,X1) = X0 ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_392,c_3,c_2,c_0]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_773,plain,
% 1.70/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 1.70/0.99      | k7_relat_1(X0_54,X0_55) = X0_54 ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_396]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1189,plain,
% 1.70/0.99      ( k7_relat_1(X0_54,X0_55) = X0_54
% 1.70/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1654,plain,
% 1.70/0.99      ( k7_relat_1(sK3,u1_struct_0(sK2)) = sK3 ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_1175,c_1189]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1,plain,
% 1.70/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 1.70/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_14,plain,
% 1.70/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.70/0.99      | ~ m1_pre_topc(X2,X1)
% 1.70/0.99      | m1_pre_topc(X2,X0)
% 1.70/0.99      | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 1.70/0.99      | ~ v2_pre_topc(X1)
% 1.70/0.99      | ~ l1_pre_topc(X1) ),
% 1.70/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_512,plain,
% 1.70/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.70/0.99      | ~ m1_pre_topc(X2,X1)
% 1.70/0.99      | m1_pre_topc(X2,X0)
% 1.70/0.99      | ~ v2_pre_topc(X1)
% 1.70/0.99      | ~ l1_pre_topc(X1)
% 1.70/0.99      | ~ v1_relat_1(X3)
% 1.70/0.99      | u1_struct_0(X0) != X4
% 1.70/0.99      | k1_relat_1(k7_relat_1(X3,X4)) != u1_struct_0(X2) ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_14]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_513,plain,
% 1.70/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.70/0.99      | ~ m1_pre_topc(X2,X1)
% 1.70/0.99      | m1_pre_topc(X0,X2)
% 1.70/0.99      | ~ v2_pre_topc(X1)
% 1.70/0.99      | ~ l1_pre_topc(X1)
% 1.70/0.99      | ~ v1_relat_1(X3)
% 1.70/0.99      | k1_relat_1(k7_relat_1(X3,u1_struct_0(X2))) != u1_struct_0(X0) ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_512]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_771,plain,
% 1.70/0.99      ( ~ m1_pre_topc(X0_53,X1_53)
% 1.70/0.99      | ~ m1_pre_topc(X2_53,X1_53)
% 1.70/0.99      | m1_pre_topc(X0_53,X2_53)
% 1.70/0.99      | ~ v2_pre_topc(X1_53)
% 1.70/0.99      | ~ l1_pre_topc(X1_53)
% 1.70/0.99      | ~ v1_relat_1(X0_54)
% 1.70/0.99      | k1_relat_1(k7_relat_1(X0_54,u1_struct_0(X2_53))) != u1_struct_0(X0_53) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_513]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1191,plain,
% 1.70/0.99      ( k1_relat_1(k7_relat_1(X0_54,u1_struct_0(X0_53))) != u1_struct_0(X1_53)
% 1.70/0.99      | m1_pre_topc(X1_53,X2_53) != iProver_top
% 1.70/0.99      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 1.70/0.99      | m1_pre_topc(X1_53,X0_53) = iProver_top
% 1.70/0.99      | v2_pre_topc(X2_53) != iProver_top
% 1.70/0.99      | l1_pre_topc(X2_53) != iProver_top
% 1.70/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_771]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1782,plain,
% 1.70/0.99      ( u1_struct_0(X0_53) != k1_relat_1(sK3)
% 1.70/0.99      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 1.70/0.99      | m1_pre_topc(X0_53,sK2) = iProver_top
% 1.70/0.99      | m1_pre_topc(sK2,X1_53) != iProver_top
% 1.70/0.99      | v2_pre_topc(X1_53) != iProver_top
% 1.70/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.70/0.99      | v1_relat_1(sK3) != iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_1654,c_1191]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_37,plain,
% 1.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_789,plain,
% 1.70/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 1.70/0.99      | v1_relat_1(X0_54) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1349,plain,
% 1.70/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | v1_relat_1(sK3) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_789]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1350,plain,
% 1.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 1.70/0.99      | v1_relat_1(sK3) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1349]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1849,plain,
% 1.70/0.99      ( l1_pre_topc(X1_53) != iProver_top
% 1.70/0.99      | v2_pre_topc(X1_53) != iProver_top
% 1.70/0.99      | m1_pre_topc(sK2,X1_53) != iProver_top
% 1.70/0.99      | m1_pre_topc(X0_53,sK2) = iProver_top
% 1.70/0.99      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 1.70/0.99      | u1_struct_0(X0_53) != k1_relat_1(sK3) ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_1782,c_37,c_1350]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1850,plain,
% 1.70/0.99      ( u1_struct_0(X0_53) != k1_relat_1(sK3)
% 1.70/0.99      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 1.70/0.99      | m1_pre_topc(X0_53,sK2) = iProver_top
% 1.70/0.99      | m1_pre_topc(sK2,X1_53) != iProver_top
% 1.70/0.99      | v2_pre_topc(X1_53) != iProver_top
% 1.70/0.99      | l1_pre_topc(X1_53) != iProver_top ),
% 1.70/0.99      inference(renaming,[status(thm)],[c_1849]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2037,plain,
% 1.70/0.99      ( m1_pre_topc(sK2,X0_53) != iProver_top
% 1.70/0.99      | m1_pre_topc(sK2,sK2) = iProver_top
% 1.70/0.99      | v2_pre_topc(X0_53) != iProver_top
% 1.70/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2011,c_1850]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_25,negated_conjecture,
% 1.70/0.99      ( v2_pre_topc(sK0) ),
% 1.70/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_28,plain,
% 1.70/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_24,negated_conjecture,
% 1.70/0.99      ( l1_pre_topc(sK0) ),
% 1.70/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_29,plain,
% 1.70/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_19,negated_conjecture,
% 1.70/0.99      ( m1_pre_topc(sK2,sK0) ),
% 1.70/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_34,plain,
% 1.70/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1357,plain,
% 1.70/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | k7_relat_1(sK3,u1_struct_0(sK2)) = sK3 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_773]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_795,plain,( X0_56 = X0_56 ),theory(equality) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1396,plain,
% 1.70/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_795]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1407,plain,
% 1.70/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_794]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1421,plain,
% 1.70/0.99      ( ~ m1_pre_topc(X0_53,sK0)
% 1.70/0.99      | m1_pre_topc(sK2,X0_53)
% 1.70/0.99      | ~ m1_pre_topc(sK2,sK0)
% 1.70/0.99      | ~ v2_pre_topc(sK0)
% 1.70/0.99      | ~ l1_pre_topc(sK0)
% 1.70/0.99      | ~ v1_relat_1(X0_54)
% 1.70/0.99      | k1_relat_1(k7_relat_1(X0_54,u1_struct_0(X0_53))) != u1_struct_0(sK2) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_771]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1426,plain,
% 1.70/0.99      ( ~ m1_pre_topc(sK2,sK0)
% 1.70/0.99      | m1_pre_topc(sK2,sK2)
% 1.70/0.99      | ~ v2_pre_topc(sK0)
% 1.70/0.99      | ~ l1_pre_topc(sK0)
% 1.70/0.99      | ~ v1_relat_1(X0_54)
% 1.70/0.99      | k1_relat_1(k7_relat_1(X0_54,u1_struct_0(sK2))) != u1_struct_0(sK2) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1421]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1427,plain,
% 1.70/0.99      ( k1_relat_1(k7_relat_1(X0_54,u1_struct_0(sK2))) != u1_struct_0(sK2)
% 1.70/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 1.70/0.99      | m1_pre_topc(sK2,sK2) = iProver_top
% 1.70/0.99      | v2_pre_topc(sK0) != iProver_top
% 1.70/0.99      | l1_pre_topc(sK0) != iProver_top
% 1.70/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1426]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1429,plain,
% 1.70/0.99      ( k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) != u1_struct_0(sK2)
% 1.70/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 1.70/0.99      | m1_pre_topc(sK2,sK2) = iProver_top
% 1.70/0.99      | v2_pre_topc(sK0) != iProver_top
% 1.70/0.99      | l1_pre_topc(sK0) != iProver_top
% 1.70/0.99      | v1_relat_1(sK3) != iProver_top ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1427]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1514,plain,
% 1.70/0.99      ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | v1_xboole_0(u1_struct_0(sK1))
% 1.70/0.99      | ~ v1_funct_1(X0_54)
% 1.70/0.99      | k1_relat_1(X0_54) = u1_struct_0(sK2) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_772]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1633,plain,
% 1.70/0.99      ( ~ v1_funct_2(k7_relat_1(X0_54,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | ~ m1_subset_1(k7_relat_1(X0_54,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | v1_xboole_0(u1_struct_0(sK1))
% 1.70/0.99      | ~ v1_funct_1(k7_relat_1(X0_54,u1_struct_0(sK2)))
% 1.70/0.99      | k1_relat_1(k7_relat_1(X0_54,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1514]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1635,plain,
% 1.70/0.99      ( ~ v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | v1_xboole_0(u1_struct_0(sK1))
% 1.70/0.99      | ~ v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
% 1.70/0.99      | k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1633]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_805,plain,
% 1.70/0.99      ( ~ v1_funct_1(X0_54) | v1_funct_1(X1_54) | X1_54 != X0_54 ),
% 1.70/0.99      theory(equality) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1711,plain,
% 1.70/0.99      ( ~ v1_funct_1(X0_54)
% 1.70/0.99      | v1_funct_1(k7_relat_1(X1_54,u1_struct_0(sK2)))
% 1.70/0.99      | k7_relat_1(X1_54,u1_struct_0(sK2)) != X0_54 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_805]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1713,plain,
% 1.70/0.99      ( v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
% 1.70/0.99      | ~ v1_funct_1(sK3)
% 1.70/0.99      | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1711]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_804,plain,
% 1.70/0.99      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 1.70/0.99      | v1_funct_2(X1_54,X2_55,X3_55)
% 1.70/0.99      | X2_55 != X0_55
% 1.70/0.99      | X3_55 != X1_55
% 1.70/0.99      | X1_54 != X0_54 ),
% 1.70/0.99      theory(equality) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1377,plain,
% 1.70/0.99      ( v1_funct_2(X0_54,X0_55,X1_55)
% 1.70/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | X1_55 != u1_struct_0(sK1)
% 1.70/0.99      | X0_55 != u1_struct_0(sK2)
% 1.70/0.99      | X0_54 != sK3 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_804]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1406,plain,
% 1.70/0.99      ( v1_funct_2(X0_54,X0_55,u1_struct_0(sK1))
% 1.70/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | X0_55 != u1_struct_0(sK2)
% 1.70/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.70/0.99      | X0_54 != sK3 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1377]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1458,plain,
% 1.70/0.99      ( v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.70/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.70/0.99      | X0_54 != sK3 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1406]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1963,plain,
% 1.70/0.99      ( v1_funct_2(k7_relat_1(X0_54,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.70/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.70/0.99      | k7_relat_1(X0_54,u1_struct_0(sK2)) != sK3 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1458]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1965,plain,
% 1.70/0.99      ( v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.70/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.70/0.99      | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1963]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_803,plain,
% 1.70/0.99      ( ~ m1_subset_1(X0_54,X0_56)
% 1.70/0.99      | m1_subset_1(X1_54,X1_56)
% 1.70/0.99      | X1_56 != X0_56
% 1.70/0.99      | X1_54 != X0_54 ),
% 1.70/0.99      theory(equality) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1360,plain,
% 1.70/0.99      ( m1_subset_1(X0_54,X0_56)
% 1.70/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | X0_56 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 1.70/0.99      | X0_54 != sK3 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_803]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1395,plain,
% 1.70/0.99      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 1.70/0.99      | X0_54 != sK3 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1360]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2336,plain,
% 1.70/0.99      ( m1_subset_1(k7_relat_1(X0_54,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 1.70/0.99      | k7_relat_1(X0_54,u1_struct_0(sK2)) != sK3 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1395]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2338,plain,
% 1.70/0.99      ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 1.70/0.99      | k7_relat_1(sK3,u1_struct_0(sK2)) != sK3 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_2336]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2391,plain,
% 1.70/0.99      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_2037,c_28,c_29,c_23,c_21,c_34,c_18,c_17,c_16,c_37,
% 1.70/0.99                 c_47,c_50,c_1350,c_1357,c_1396,c_1407,c_1429,c_1459,
% 1.70/0.99                 c_1635,c_1713,c_1965,c_2338]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_783,negated_conjecture,
% 1.70/0.99      ( m1_pre_topc(sK2,sK0) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1178,plain,
% 1.70/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_12,plain,
% 1.70/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.70/0.99      | ~ m1_pre_topc(X3,X1)
% 1.70/0.99      | ~ m1_pre_topc(X3,X4)
% 1.70/0.99      | ~ m1_pre_topc(X1,X4)
% 1.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.70/0.99      | ~ v2_pre_topc(X2)
% 1.70/0.99      | ~ v2_pre_topc(X4)
% 1.70/0.99      | v2_struct_0(X4)
% 1.70/0.99      | v2_struct_0(X2)
% 1.70/0.99      | ~ l1_pre_topc(X4)
% 1.70/0.99      | ~ l1_pre_topc(X2)
% 1.70/0.99      | ~ v1_funct_1(X0)
% 1.70/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 1.70/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_787,plain,
% 1.70/0.99      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 1.70/0.99      | ~ m1_pre_topc(X2_53,X0_53)
% 1.70/0.99      | ~ m1_pre_topc(X2_53,X3_53)
% 1.70/0.99      | ~ m1_pre_topc(X0_53,X3_53)
% 1.70/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 1.70/0.99      | ~ v2_pre_topc(X1_53)
% 1.70/0.99      | ~ v2_pre_topc(X3_53)
% 1.70/0.99      | v2_struct_0(X3_53)
% 1.70/0.99      | v2_struct_0(X1_53)
% 1.70/0.99      | ~ l1_pre_topc(X1_53)
% 1.70/0.99      | ~ l1_pre_topc(X3_53)
% 1.70/0.99      | ~ v1_funct_1(X0_54)
% 1.70/0.99      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_54) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1174,plain,
% 1.70/0.99      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_54)
% 1.70/0.99      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 1.70/0.99      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 1.70/0.99      | m1_pre_topc(X2_53,X3_53) != iProver_top
% 1.70/0.99      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 1.70/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 1.70/0.99      | v2_pre_topc(X1_53) != iProver_top
% 1.70/0.99      | v2_pre_topc(X3_53) != iProver_top
% 1.70/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.70/0.99      | v2_struct_0(X3_53) = iProver_top
% 1.70/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.70/0.99      | l1_pre_topc(X3_53) != iProver_top
% 1.70/0.99      | v1_funct_1(X0_54) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_787]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1800,plain,
% 1.70/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK2,X0_53,sK3)
% 1.70/0.99      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 1.70/0.99      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 1.70/0.99      | m1_pre_topc(X0_53,sK2) != iProver_top
% 1.70/0.99      | m1_pre_topc(sK2,X1_53) != iProver_top
% 1.70/0.99      | v2_pre_topc(X1_53) != iProver_top
% 1.70/0.99      | v2_pre_topc(sK1) != iProver_top
% 1.70/0.99      | v2_struct_0(X1_53) = iProver_top
% 1.70/0.99      | v2_struct_0(sK1) = iProver_top
% 1.70/0.99      | l1_pre_topc(X1_53) != iProver_top
% 1.70/0.99      | l1_pre_topc(sK1) != iProver_top
% 1.70/0.99      | v1_funct_1(sK3) != iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_1175,c_1174]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_8,plain,
% 1.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.99      | ~ v1_funct_1(X0)
% 1.70/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 1.70/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_788,plain,
% 1.70/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 1.70/0.99      | ~ v1_funct_1(X0_54)
% 1.70/0.99      | k2_partfun1(X0_55,X1_55,X0_54,X2_55) = k7_relat_1(X0_54,X2_55) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1173,plain,
% 1.70/0.99      ( k2_partfun1(X0_55,X1_55,X0_54,X2_55) = k7_relat_1(X0_54,X2_55)
% 1.70/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 1.70/0.99      | v1_funct_1(X0_54) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1533,plain,
% 1.70/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_55) = k7_relat_1(sK3,X0_55)
% 1.70/0.99      | v1_funct_1(sK3) != iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_1175,c_1173]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1372,plain,
% 1.70/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | ~ v1_funct_1(sK3)
% 1.70/0.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_55) = k7_relat_1(sK3,X0_55) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_788]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1587,plain,
% 1.70/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_55) = k7_relat_1(sK3,X0_55) ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_1533,c_18,c_16,c_1372]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1801,plain,
% 1.70/0.99      ( k3_tmap_1(X0_53,sK1,sK2,X1_53,sK3) = k7_relat_1(sK3,u1_struct_0(X1_53))
% 1.70/0.99      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 1.70/0.99      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 1.70/0.99      | m1_pre_topc(X1_53,sK2) != iProver_top
% 1.70/0.99      | m1_pre_topc(sK2,X0_53) != iProver_top
% 1.70/0.99      | v2_pre_topc(X0_53) != iProver_top
% 1.70/0.99      | v2_pre_topc(sK1) != iProver_top
% 1.70/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.70/0.99      | v2_struct_0(sK1) = iProver_top
% 1.70/0.99      | l1_pre_topc(X0_53) != iProver_top
% 1.70/0.99      | l1_pre_topc(sK1) != iProver_top
% 1.70/0.99      | v1_funct_1(sK3) != iProver_top ),
% 1.70/0.99      inference(demodulation,[status(thm)],[c_1800,c_1587]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_30,plain,
% 1.70/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_22,negated_conjecture,
% 1.70/0.99      ( v2_pre_topc(sK1) ),
% 1.70/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_31,plain,
% 1.70/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_32,plain,
% 1.70/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_35,plain,
% 1.70/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_36,plain,
% 1.70/0.99      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1862,plain,
% 1.70/0.99      ( v2_struct_0(X0_53) = iProver_top
% 1.70/0.99      | k3_tmap_1(X0_53,sK1,sK2,X1_53,sK3) = k7_relat_1(sK3,u1_struct_0(X1_53))
% 1.70/0.99      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 1.70/0.99      | m1_pre_topc(X1_53,sK2) != iProver_top
% 1.70/0.99      | m1_pre_topc(sK2,X0_53) != iProver_top
% 1.70/0.99      | v2_pre_topc(X0_53) != iProver_top
% 1.70/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_1801,c_30,c_31,c_32,c_35,c_36]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1863,plain,
% 1.70/0.99      ( k3_tmap_1(X0_53,sK1,sK2,X1_53,sK3) = k7_relat_1(sK3,u1_struct_0(X1_53))
% 1.70/0.99      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 1.70/0.99      | m1_pre_topc(X1_53,sK2) != iProver_top
% 1.70/0.99      | m1_pre_topc(sK2,X0_53) != iProver_top
% 1.70/0.99      | v2_pre_topc(X0_53) != iProver_top
% 1.70/0.99      | v2_struct_0(X0_53) = iProver_top
% 1.70/0.99      | l1_pre_topc(X0_53) != iProver_top ),
% 1.70/0.99      inference(renaming,[status(thm)],[c_1862]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1875,plain,
% 1.70/0.99      ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = k7_relat_1(sK3,u1_struct_0(sK2))
% 1.70/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 1.70/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 1.70/0.99      | v2_pre_topc(sK0) != iProver_top
% 1.70/0.99      | v2_struct_0(sK0) = iProver_top
% 1.70/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_1178,c_1863]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1876,plain,
% 1.70/0.99      ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = sK3
% 1.70/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 1.70/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 1.70/0.99      | v2_pre_topc(sK0) != iProver_top
% 1.70/0.99      | v2_struct_0(sK0) = iProver_top
% 1.70/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 1.70/0.99      inference(light_normalisation,[status(thm)],[c_1875,c_1654]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_26,negated_conjecture,
% 1.70/0.99      ( ~ v2_struct_0(sK0) ),
% 1.70/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_27,plain,
% 1.70/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1938,plain,
% 1.70/0.99      ( m1_pre_topc(sK2,sK2) != iProver_top
% 1.70/0.99      | k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = sK3 ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_1876,c_27,c_28,c_29,c_34]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1939,plain,
% 1.70/0.99      ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = sK3
% 1.70/0.99      | m1_pre_topc(sK2,sK2) != iProver_top ),
% 1.70/0.99      inference(renaming,[status(thm)],[c_1938]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2397,plain,
% 1.70/0.99      ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = sK3 ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2391,c_1939]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_9,plain,
% 1.70/0.99      ( r2_funct_2(X0,X1,X2,X2)
% 1.70/0.99      | ~ v1_funct_2(X2,X0,X1)
% 1.70/0.99      | ~ v1_funct_2(X3,X0,X1)
% 1.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.70/0.99      | ~ v1_funct_1(X2)
% 1.70/0.99      | ~ v1_funct_1(X3) ),
% 1.70/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_15,negated_conjecture,
% 1.70/0.99      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) ),
% 1.70/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_337,plain,
% 1.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.70/0.99      | ~ v1_funct_2(X3,X1,X2)
% 1.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.70/0.99      | ~ v1_funct_1(X0)
% 1.70/0.99      | ~ v1_funct_1(X3)
% 1.70/0.99      | k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != X0
% 1.70/0.99      | u1_struct_0(sK1) != X2
% 1.70/0.99      | u1_struct_0(sK2) != X1
% 1.70/0.99      | sK3 != X0 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_338,plain,
% 1.70/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | ~ v1_funct_1(X0)
% 1.70/0.99      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
% 1.70/0.99      | sK3 != k3_tmap_1(sK0,sK1,sK2,sK2,sK3) ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_337]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_774,plain,
% 1.70/0.99      ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | ~ v1_funct_1(X0_54)
% 1.70/0.99      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
% 1.70/0.99      | sK3 != k3_tmap_1(sK0,sK1,sK2,sK2,sK3) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_338]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_791,plain,
% 1.70/0.99      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
% 1.70/0.99      | sP0_iProver_split
% 1.70/0.99      | sK3 != k3_tmap_1(sK0,sK1,sK2,sK2,sK3) ),
% 1.70/0.99      inference(splitting,
% 1.70/0.99                [splitting(split),new_symbols(definition,[])],
% 1.70/0.99                [c_774]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1187,plain,
% 1.70/0.99      ( sK3 != k3_tmap_1(sK0,sK1,sK2,sK2,sK3)
% 1.70/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 1.70/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 1.70/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) != iProver_top
% 1.70/0.99      | sP0_iProver_split = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_790,plain,
% 1.70/0.99      ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | ~ v1_funct_1(X0_54)
% 1.70/0.99      | ~ sP0_iProver_split ),
% 1.70/0.99      inference(splitting,
% 1.70/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.70/0.99                [c_774]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1188,plain,
% 1.70/0.99      ( v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 1.70/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 1.70/0.99      | v1_funct_1(X0_54) != iProver_top
% 1.70/0.99      | sP0_iProver_split != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1271,plain,
% 1.70/0.99      ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != sK3
% 1.70/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 1.70/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 1.70/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) != iProver_top ),
% 1.70/0.99      inference(forward_subsumption_resolution,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_1187,c_1188]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1352,plain,
% 1.70/0.99      ( ~ v1_funct_1(X0_54)
% 1.70/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
% 1.70/0.99      | k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != X0_54 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_805]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1353,plain,
% 1.70/0.99      ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != X0_54
% 1.70/0.99      | v1_funct_1(X0_54) != iProver_top
% 1.70/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1352]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1355,plain,
% 1.70/0.99      ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != sK3
% 1.70/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) = iProver_top
% 1.70/0.99      | v1_funct_1(sK3) != iProver_top ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1353]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1644,plain,
% 1.70/0.99      ( m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 1.70/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 1.70/0.99      | k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != sK3 ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_1271,c_35,c_1355]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1645,plain,
% 1.70/0.99      ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != sK3
% 1.70/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 1.70/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 1.70/0.99      inference(renaming,[status(thm)],[c_1644]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2015,plain,
% 1.70/0.99      ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) != sK3
% 1.70/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
% 1.70/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
% 1.70/0.99      inference(demodulation,[status(thm)],[c_2011,c_1645]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2413,plain,
% 1.70/0.99      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
% 1.70/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_2015,c_27,c_28,c_29,c_23,c_21,c_34,c_18,c_17,c_16,
% 1.70/0.99                 c_37,c_47,c_50,c_1350,c_1357,c_1396,c_1407,c_1429,
% 1.70/0.99                 c_1459,c_1635,c_1713,c_1876,c_1965,c_2338]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2711,plain,
% 1.70/0.99      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) != iProver_top
% 1.70/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) != iProver_top ),
% 1.70/0.99      inference(demodulation,[status(thm)],[c_2397,c_2413]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1442,plain,
% 1.70/0.99      ( m1_subset_1(X0_54,X0_56)
% 1.70/0.99      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | X0_56 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 1.70/0.99      | X0_54 != X1_54 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_803]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1968,plain,
% 1.70/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.70/0.99      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))))
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 1.70/0.99      | X1_54 != X0_54 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1442]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1970,plain,
% 1.70/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 1.70/0.99      | X0_54 != X1_54
% 1.70/0.99      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 1.70/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1968]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1972,plain,
% 1.70/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 1.70/0.99      | sK3 != sK3
% 1.70/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 1.70/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1970]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_802,plain,
% 1.70/0.99      ( X0_57 != X1_57 | k1_zfmisc_1(X0_57) = k1_zfmisc_1(X1_57) ),
% 1.70/0.99      theory(equality) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1400,plain,
% 1.70/0.99      ( X0_57 != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | k1_zfmisc_1(X0_57) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_802]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1451,plain,
% 1.70/0.99      ( k2_zfmisc_1(X0_55,X1_55) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1400]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1581,plain,
% 1.70/0.99      ( k2_zfmisc_1(X0_55,u1_struct_0(sK1)) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1451]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1925,plain,
% 1.70/0.99      ( k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1581]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_801,plain,
% 1.70/0.99      ( k2_zfmisc_1(X0_55,X1_55) = k2_zfmisc_1(X2_55,X3_55)
% 1.70/0.99      | X0_55 != X2_55
% 1.70/0.99      | X1_55 != X3_55 ),
% 1.70/0.99      theory(equality) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1452,plain,
% 1.70/0.99      ( k2_zfmisc_1(X0_55,X1_55) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | X1_55 != u1_struct_0(sK1)
% 1.70/0.99      | X0_55 != u1_struct_0(sK2) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_801]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1524,plain,
% 1.70/0.99      ( k2_zfmisc_1(X0_55,u1_struct_0(sK1)) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | X0_55 != u1_struct_0(sK2)
% 1.70/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1452]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1757,plain,
% 1.70/0.99      ( k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK1)) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.70/0.99      | k1_relat_1(sK3) != u1_struct_0(sK2) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1524]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1464,plain,
% 1.70/0.99      ( v1_funct_2(X0_54,k1_relat_1(sK3),u1_struct_0(sK1))
% 1.70/0.99      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 1.70/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.70/0.99      | k1_relat_1(sK3) != u1_struct_0(sK2)
% 1.70/0.99      | X0_54 != sK3 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1406]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1465,plain,
% 1.70/0.99      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.70/0.99      | k1_relat_1(sK3) != u1_struct_0(sK2)
% 1.70/0.99      | X0_54 != sK3
% 1.70/0.99      | v1_funct_2(X0_54,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
% 1.70/0.99      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1464]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1467,plain,
% 1.70/0.99      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.70/0.99      | k1_relat_1(sK3) != u1_struct_0(sK2)
% 1.70/0.99      | sK3 != sK3
% 1.70/0.99      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 1.70/0.99      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1465]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_793,plain,( X0_54 = X0_54 ),theory(equality) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_820,plain,
% 1.70/0.99      ( sK3 = sK3 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_793]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(contradiction,plain,
% 1.70/0.99      ( $false ),
% 1.70/0.99      inference(minisat,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_2711,c_1972,c_1925,c_1757,c_1467,c_1407,c_1365,c_820,
% 1.70/0.99                 c_50,c_47,c_37,c_16,c_36,c_17,c_18,c_21,c_23]) ).
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.70/0.99  
% 1.70/0.99  ------                               Statistics
% 1.70/0.99  
% 1.70/0.99  ------ General
% 1.70/0.99  
% 1.70/0.99  abstr_ref_over_cycles:                  0
% 1.70/0.99  abstr_ref_under_cycles:                 0
% 1.70/0.99  gc_basic_clause_elim:                   0
% 1.70/0.99  forced_gc_time:                         0
% 1.70/0.99  parsing_time:                           0.011
% 1.70/0.99  unif_index_cands_time:                  0.
% 1.70/0.99  unif_index_add_time:                    0.
% 1.70/0.99  orderings_time:                         0.
% 1.70/0.99  out_proof_time:                         0.012
% 1.70/0.99  total_time:                             0.126
% 1.70/0.99  num_of_symbols:                         59
% 1.70/0.99  num_of_terms:                           2142
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing
% 1.70/0.99  
% 1.70/0.99  num_of_splits:                          1
% 1.70/0.99  num_of_split_atoms:                     1
% 1.70/0.99  num_of_reused_defs:                     0
% 1.70/0.99  num_eq_ax_congr_red:                    23
% 1.70/0.99  num_of_sem_filtered_clauses:            2
% 1.70/0.99  num_of_subtypes:                        5
% 1.70/0.99  monotx_restored_types:                  0
% 1.70/0.99  sat_num_of_epr_types:                   0
% 1.70/0.99  sat_num_of_non_cyclic_types:            0
% 1.70/0.99  sat_guarded_non_collapsed_types:        2
% 1.70/0.99  num_pure_diseq_elim:                    0
% 1.70/0.99  simp_replaced_by:                       0
% 1.70/0.99  res_preprocessed:                       117
% 1.70/0.99  prep_upred:                             0
% 1.70/0.99  prep_unflattend:                        13
% 1.70/0.99  smt_new_axioms:                         0
% 1.70/0.99  pred_elim_cands:                        9
% 1.70/0.99  pred_elim:                              5
% 1.70/0.99  pred_elim_cl:                           7
% 1.70/0.99  pred_elim_cycles:                       11
% 1.70/0.99  merged_defs:                            0
% 1.70/0.99  merged_defs_ncl:                        0
% 1.70/0.99  bin_hyper_res:                          0
% 1.70/0.99  prep_cycles:                            4
% 1.70/0.99  pred_elim_time:                         0.008
% 1.70/0.99  splitting_time:                         0.
% 1.70/0.99  sem_filter_time:                        0.
% 1.70/0.99  monotx_time:                            0.
% 1.70/0.99  subtype_inf_time:                       0.001
% 1.70/0.99  
% 1.70/0.99  ------ Problem properties
% 1.70/0.99  
% 1.70/0.99  clauses:                                20
% 1.70/0.99  conjectures:                            11
% 1.70/0.99  epr:                                    9
% 1.70/0.99  horn:                                   18
% 1.70/0.99  ground:                                 12
% 1.70/0.99  unary:                                  11
% 1.70/0.99  binary:                                 2
% 1.70/0.99  lits:                                   55
% 1.70/0.99  lits_eq:                                6
% 1.70/0.99  fd_pure:                                0
% 1.70/0.99  fd_pseudo:                              0
% 1.70/0.99  fd_cond:                                0
% 1.70/0.99  fd_pseudo_cond:                         1
% 1.70/0.99  ac_symbols:                             0
% 1.70/0.99  
% 1.70/0.99  ------ Propositional Solver
% 1.70/0.99  
% 1.70/0.99  prop_solver_calls:                      30
% 1.70/0.99  prop_fast_solver_calls:                 919
% 1.70/0.99  smt_solver_calls:                       0
% 1.70/0.99  smt_fast_solver_calls:                  0
% 1.70/0.99  prop_num_of_clauses:                    624
% 1.70/0.99  prop_preprocess_simplified:             3301
% 1.70/0.99  prop_fo_subsumed:                       33
% 1.70/0.99  prop_solver_time:                       0.
% 1.70/0.99  smt_solver_time:                        0.
% 1.70/0.99  smt_fast_solver_time:                   0.
% 1.70/0.99  prop_fast_solver_time:                  0.
% 1.70/0.99  prop_unsat_core_time:                   0.
% 1.70/0.99  
% 1.70/0.99  ------ QBF
% 1.70/0.99  
% 1.70/0.99  qbf_q_res:                              0
% 1.70/0.99  qbf_num_tautologies:                    0
% 1.70/0.99  qbf_prep_cycles:                        0
% 1.70/0.99  
% 1.70/0.99  ------ BMC1
% 1.70/0.99  
% 1.70/0.99  bmc1_current_bound:                     -1
% 1.70/0.99  bmc1_last_solved_bound:                 -1
% 1.70/0.99  bmc1_unsat_core_size:                   -1
% 1.70/0.99  bmc1_unsat_core_parents_size:           -1
% 1.70/0.99  bmc1_merge_next_fun:                    0
% 1.70/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.70/0.99  
% 1.70/0.99  ------ Instantiation
% 1.70/0.99  
% 1.70/0.99  inst_num_of_clauses:                    214
% 1.70/0.99  inst_num_in_passive:                    24
% 1.70/0.99  inst_num_in_active:                     180
% 1.70/0.99  inst_num_in_unprocessed:                10
% 1.70/0.99  inst_num_of_loops:                      200
% 1.70/0.99  inst_num_of_learning_restarts:          0
% 1.70/0.99  inst_num_moves_active_passive:          12
% 1.70/0.99  inst_lit_activity:                      0
% 1.70/0.99  inst_lit_activity_moves:                0
% 1.70/0.99  inst_num_tautologies:                   0
% 1.70/0.99  inst_num_prop_implied:                  0
% 1.70/0.99  inst_num_existing_simplified:           0
% 1.70/0.99  inst_num_eq_res_simplified:             0
% 1.70/0.99  inst_num_child_elim:                    0
% 1.70/0.99  inst_num_of_dismatching_blockings:      49
% 1.70/0.99  inst_num_of_non_proper_insts:           286
% 1.70/0.99  inst_num_of_duplicates:                 0
% 1.70/0.99  inst_inst_num_from_inst_to_res:         0
% 1.70/0.99  inst_dismatching_checking_time:         0.
% 1.70/0.99  
% 1.70/0.99  ------ Resolution
% 1.70/0.99  
% 1.70/0.99  res_num_of_clauses:                     0
% 1.70/0.99  res_num_in_passive:                     0
% 1.70/0.99  res_num_in_active:                      0
% 1.70/0.99  res_num_of_loops:                       121
% 1.70/0.99  res_forward_subset_subsumed:            43
% 1.70/0.99  res_backward_subset_subsumed:           0
% 1.70/0.99  res_forward_subsumed:                   0
% 1.70/0.99  res_backward_subsumed:                  0
% 1.70/0.99  res_forward_subsumption_resolution:     1
% 1.70/0.99  res_backward_subsumption_resolution:    0
% 1.70/0.99  res_clause_to_clause_subsumption:       60
% 1.70/0.99  res_orphan_elimination:                 0
% 1.70/0.99  res_tautology_del:                      58
% 1.70/0.99  res_num_eq_res_simplified:              0
% 1.70/0.99  res_num_sel_changes:                    0
% 1.70/0.99  res_moves_from_active_to_pass:          0
% 1.70/0.99  
% 1.70/0.99  ------ Superposition
% 1.70/0.99  
% 1.70/0.99  sup_time_total:                         0.
% 1.70/0.99  sup_time_generating:                    0.
% 1.70/0.99  sup_time_sim_full:                      0.
% 1.70/0.99  sup_time_sim_immed:                     0.
% 1.70/0.99  
% 1.70/0.99  sup_num_of_clauses:                     34
% 1.70/0.99  sup_num_in_active:                      32
% 1.70/0.99  sup_num_in_passive:                     2
% 1.70/0.99  sup_num_of_loops:                       39
% 1.70/0.99  sup_fw_superposition:                   10
% 1.70/0.99  sup_bw_superposition:                   12
% 1.70/0.99  sup_immediate_simplified:               10
% 1.70/0.99  sup_given_eliminated:                   0
% 1.70/0.99  comparisons_done:                       0
% 1.70/0.99  comparisons_avoided:                    0
% 1.70/0.99  
% 1.70/0.99  ------ Simplifications
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  sim_fw_subset_subsumed:                 1
% 1.70/0.99  sim_bw_subset_subsumed:                 1
% 1.70/0.99  sim_fw_subsumed:                        1
% 1.70/0.99  sim_bw_subsumed:                        0
% 1.70/0.99  sim_fw_subsumption_res:                 2
% 1.70/0.99  sim_bw_subsumption_res:                 0
% 1.70/0.99  sim_tautology_del:                      0
% 1.70/0.99  sim_eq_tautology_del:                   1
% 1.70/0.99  sim_eq_res_simp:                        0
% 1.70/0.99  sim_fw_demodulated:                     2
% 1.70/0.99  sim_bw_demodulated:                     6
% 1.70/0.99  sim_light_normalised:                   6
% 1.70/0.99  sim_joinable_taut:                      0
% 1.70/0.99  sim_joinable_simp:                      0
% 1.70/0.99  sim_ac_normalised:                      0
% 1.70/0.99  sim_smt_subsumption:                    0
% 1.70/0.99  
%------------------------------------------------------------------------------
