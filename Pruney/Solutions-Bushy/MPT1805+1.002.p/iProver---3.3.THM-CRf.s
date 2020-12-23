%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1805+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:30 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 521 expanded)
%              Number of clauses        :   66 ( 120 expanded)
%              Number of leaves         :   13 ( 137 expanded)
%              Depth                    :   15
%              Number of atoms          :  743 (3977 expanded)
%              Number of equality atoms :   27 (  41 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   18 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
              & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(X0,sK2)))))
          | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),sK2,k8_tmap_1(X0,sK2))
          | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(X0,sK2)))
          | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2)) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
              | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK1,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),X1,k8_tmap_1(sK1,X1))
            | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK1,X1)))
            | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1)) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
      | ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2))
      | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) )
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f43,f42])).

fof(f69,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK0(X0,X1,X2))
                    & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | ~ r1_tmap_1(X1,X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_787,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | m1_subset_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X0_48)
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1264,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(X0_48),u1_struct_0(X1_48))
    | m1_subset_1(k2_tmap_1(X0_48,X1_48,k9_tmap_1(sK1,sK2),X2_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X0_48)
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_1305,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ l1_struct_0(X0_48)
    | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1264])).

cnf(c_1307,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_786,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | v1_funct_2(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),u1_struct_0(X2_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X0_48)
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1255,plain,
    ( v1_funct_2(k2_tmap_1(X0_48,X1_48,k9_tmap_1(sK1,sK2),X2_48),u1_struct_0(X2_48),u1_struct_0(X1_48))
    | ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X0_48)
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_1300,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),X0_48),u1_struct_0(X0_48),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ l1_struct_0(X0_48)
    | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1255])).

cnf(c_1302,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_785,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X0_48)
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1250,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X0_48)
    | v1_funct_1(k2_tmap_1(X0_48,X1_48,k9_tmap_1(sK1,sK2),X2_48))
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_1295,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ l1_struct_0(X0_48)
    | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),X0_48))
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1250])).

cnf(c_1297,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_12,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_405,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_406,plain,
    ( v2_struct_0(sK1)
    | l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_408,plain,
    ( l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_25,c_24,c_23])).

cnf(c_658,plain,
    ( l1_struct_0(X0)
    | k8_tmap_1(sK1,sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_408])).

cnf(c_659,plain,
    ( l1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_644,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_645,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_18,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X2,X1,X0),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_20,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_536,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | m1_subset_1(sK0(X2,X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) != X0
    | k8_tmap_1(sK1,sK2) != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_537,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | m1_subset_1(sK0(k8_tmap_1(sK1,sK2),sK2,k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)),u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_361,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(k8_tmap_1(X0,X1))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_362,plain,
    ( ~ v2_struct_0(k8_tmap_1(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_372,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_373,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_394,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1))
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_395,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_416,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_417,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_17,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK0(X1,X0,X2))
    | v5_pre_topc(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_16,plain,
    ( r1_tmap_1(X0,k8_tmap_1(X1,X0),k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_343,plain,
    ( r1_tmap_1(X0,k8_tmap_1(X1,X0),k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_344,plain,
    ( r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_348,plain,
    ( r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_25,c_24,c_23,c_22])).

cnf(c_511,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2) != X0
    | sK0(X2,X1,X0) != X3
    | k8_tmap_1(sK1,sK2) != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_348])).

cnf(c_512,plain,
    ( v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k8_tmap_1(sK1,sK2),sK2,k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)),u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_514,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k8_tmap_1(sK1,sK2),sK2,k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_25,c_24,c_23,c_22,c_20,c_362,c_373,c_395,c_406,c_417])).

cnf(c_539,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_25,c_24,c_23,c_22,c_362,c_373,c_395,c_406,c_417,c_514])).

cnf(c_540,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
    inference(renaming,[status(thm)],[c_539])).

cnf(c_9,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_471,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_472,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_10,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_460,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_461,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_383,plain,
    ( v2_struct_0(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_384,plain,
    ( v2_struct_0(sK1)
    | v1_funct_1(k9_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_52,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1307,c_1302,c_1297,c_659,c_645,c_540,c_472,c_461,c_384,c_373,c_52,c_23,c_24,c_25])).


%------------------------------------------------------------------------------
