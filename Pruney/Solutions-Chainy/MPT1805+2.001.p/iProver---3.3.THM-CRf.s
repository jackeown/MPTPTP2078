%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:11 EST 2020

% Result     : Theorem 0.97s
% Output     : CNFRefutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 500 expanded)
%              Number of clauses        :   52 (  99 expanded)
%              Number of leaves         :   13 ( 137 expanded)
%              Depth                    :   13
%              Number of atoms          :  648 (3845 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal clause size      :   18 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
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
    inference(pure_predicate_removal,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f68,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
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

fof(f62,plain,(
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

fof(f69,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
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

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f63,plain,(
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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_507,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | m1_subset_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
    | ~ v1_funct_1(X0_49)
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_564,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(X0_48),u1_struct_0(X1_48))
    | m1_subset_1(k2_tmap_1(X0_48,X1_48,k9_tmap_1(sK1,sK2),X2_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X0_48) ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_636,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
    | ~ l1_struct_0(X0_48)
    | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_638,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
    | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_506,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | v1_funct_2(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),u1_struct_0(X2_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ v1_funct_1(X0_49)
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_559,plain,
    ( v1_funct_2(k2_tmap_1(X0_48,X1_48,k9_tmap_1(sK1,sK2),X2_48),u1_struct_0(X2_48),u1_struct_0(X1_48))
    | ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X0_48) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_590,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),X0_48),u1_struct_0(X0_48),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
    | ~ l1_struct_0(X0_48)
    | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_592,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
    | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_505,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48))
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_554,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | v1_funct_1(k2_tmap_1(X0_48,X1_48,k9_tmap_1(sK1,sK2),X2_48))
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X2_48)
    | ~ l1_struct_0(X0_48) ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_569,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
    | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_1,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_300,plain,
    ( v2_struct_0(sK1)
    | l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_8,c_20])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_302,plain,
    ( l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_300,c_24,c_23,c_22])).

cnf(c_426,plain,
    ( l1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_1,c_302])).

cnf(c_414,plain,
    ( l1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_1,c_22])).

cnf(c_17,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X2,X1,X0),u1_struct_0(X1))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_19,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_394,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | m1_subset_1(sK0(k8_tmap_1(sK1,sK2),sK2,k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_17,c_19])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_270,plain,
    ( ~ v2_struct_0(k8_tmap_1(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_14,c_20])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_290,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_9,c_20])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_310,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_2,c_20])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_320,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_0,c_20])).

cnf(c_16,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK0(X1,X0,X2))
    | v5_pre_topc(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_15,plain,
    ( r1_tmap_1(X0,k8_tmap_1(X1,X0),k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_253,plain,
    ( r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_15,c_20])).

cnf(c_257,plain,
    ( r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_253,c_24,c_23,c_22,c_21])).

cnf(c_370,plain,
    ( v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k8_tmap_1(sK1,sK2),sK2,k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_16,c_257])).

cnf(c_372,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k8_tmap_1(sK1,sK2),sK2,k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_24,c_23,c_22,c_21,c_19,c_270,c_290,c_300,c_310,c_320])).

cnf(c_396,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_24,c_23,c_22,c_21,c_270,c_290,c_300,c_310,c_320,c_372])).

cnf(c_397,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
    inference(renaming,[status(thm)],[c_396])).

cnf(c_10,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_340,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_10,c_20])).

cnf(c_11,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_330,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_11,c_20])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_280,plain,
    ( v1_funct_1(k9_tmap_1(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_12,c_20])).

cnf(c_77,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_638,c_592,c_569,c_426,c_414,c_397,c_340,c_330,c_310,c_280,c_77,c_22,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 20:35:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 0.97/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.97/1.00  
% 0.97/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.97/1.00  
% 0.97/1.00  ------  iProver source info
% 0.97/1.00  
% 0.97/1.00  git: date: 2020-06-30 10:37:57 +0100
% 0.97/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.97/1.00  git: non_committed_changes: false
% 0.97/1.00  git: last_make_outside_of_git: false
% 0.97/1.00  
% 0.97/1.00  ------ 
% 0.97/1.00  
% 0.97/1.00  ------ Input Options
% 0.97/1.00  
% 0.97/1.00  --out_options                           all
% 0.97/1.00  --tptp_safe_out                         true
% 0.97/1.00  --problem_path                          ""
% 0.97/1.00  --include_path                          ""
% 0.97/1.00  --clausifier                            res/vclausify_rel
% 0.97/1.00  --clausifier_options                    --mode clausify
% 0.97/1.00  --stdin                                 false
% 0.97/1.00  --stats_out                             all
% 0.97/1.00  
% 0.97/1.00  ------ General Options
% 0.97/1.00  
% 0.97/1.00  --fof                                   false
% 0.97/1.00  --time_out_real                         305.
% 0.97/1.00  --time_out_virtual                      -1.
% 0.97/1.00  --symbol_type_check                     false
% 0.97/1.00  --clausify_out                          false
% 0.97/1.00  --sig_cnt_out                           false
% 0.97/1.00  --trig_cnt_out                          false
% 0.97/1.00  --trig_cnt_out_tolerance                1.
% 0.97/1.00  --trig_cnt_out_sk_spl                   false
% 0.97/1.00  --abstr_cl_out                          false
% 0.97/1.00  
% 0.97/1.00  ------ Global Options
% 0.97/1.00  
% 0.97/1.00  --schedule                              default
% 0.97/1.00  --add_important_lit                     false
% 0.97/1.00  --prop_solver_per_cl                    1000
% 0.97/1.00  --min_unsat_core                        false
% 0.97/1.00  --soft_assumptions                      false
% 0.97/1.00  --soft_lemma_size                       3
% 0.97/1.00  --prop_impl_unit_size                   0
% 0.97/1.00  --prop_impl_unit                        []
% 0.97/1.00  --share_sel_clauses                     true
% 0.97/1.00  --reset_solvers                         false
% 0.97/1.00  --bc_imp_inh                            [conj_cone]
% 0.97/1.00  --conj_cone_tolerance                   3.
% 0.97/1.00  --extra_neg_conj                        none
% 0.97/1.00  --large_theory_mode                     true
% 0.97/1.00  --prolific_symb_bound                   200
% 0.97/1.00  --lt_threshold                          2000
% 0.97/1.00  --clause_weak_htbl                      true
% 0.97/1.00  --gc_record_bc_elim                     false
% 0.97/1.00  
% 0.97/1.00  ------ Preprocessing Options
% 0.97/1.00  
% 0.97/1.00  --preprocessing_flag                    true
% 0.97/1.00  --time_out_prep_mult                    0.1
% 0.97/1.00  --splitting_mode                        input
% 0.97/1.00  --splitting_grd                         true
% 0.97/1.00  --splitting_cvd                         false
% 0.97/1.00  --splitting_cvd_svl                     false
% 0.97/1.00  --splitting_nvd                         32
% 0.97/1.00  --sub_typing                            true
% 0.97/1.00  --prep_gs_sim                           true
% 0.97/1.00  --prep_unflatten                        true
% 0.97/1.00  --prep_res_sim                          true
% 0.97/1.00  --prep_upred                            true
% 0.97/1.00  --prep_sem_filter                       exhaustive
% 0.97/1.00  --prep_sem_filter_out                   false
% 0.97/1.00  --pred_elim                             true
% 0.97/1.00  --res_sim_input                         true
% 0.97/1.00  --eq_ax_congr_red                       true
% 0.97/1.00  --pure_diseq_elim                       true
% 0.97/1.00  --brand_transform                       false
% 0.97/1.00  --non_eq_to_eq                          false
% 0.97/1.00  --prep_def_merge                        true
% 0.97/1.00  --prep_def_merge_prop_impl              false
% 0.97/1.00  --prep_def_merge_mbd                    true
% 0.97/1.00  --prep_def_merge_tr_red                 false
% 0.97/1.00  --prep_def_merge_tr_cl                  false
% 0.97/1.00  --smt_preprocessing                     true
% 0.97/1.00  --smt_ac_axioms                         fast
% 0.97/1.00  --preprocessed_out                      false
% 0.97/1.00  --preprocessed_stats                    false
% 0.97/1.00  
% 0.97/1.00  ------ Abstraction refinement Options
% 0.97/1.00  
% 0.97/1.00  --abstr_ref                             []
% 0.97/1.00  --abstr_ref_prep                        false
% 0.97/1.00  --abstr_ref_until_sat                   false
% 0.97/1.00  --abstr_ref_sig_restrict                funpre
% 0.97/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.97/1.00  --abstr_ref_under                       []
% 0.97/1.00  
% 0.97/1.00  ------ SAT Options
% 0.97/1.00  
% 0.97/1.00  --sat_mode                              false
% 0.97/1.00  --sat_fm_restart_options                ""
% 0.97/1.00  --sat_gr_def                            false
% 0.97/1.00  --sat_epr_types                         true
% 0.97/1.00  --sat_non_cyclic_types                  false
% 0.97/1.00  --sat_finite_models                     false
% 0.97/1.00  --sat_fm_lemmas                         false
% 0.97/1.00  --sat_fm_prep                           false
% 0.97/1.00  --sat_fm_uc_incr                        true
% 0.97/1.00  --sat_out_model                         small
% 0.97/1.00  --sat_out_clauses                       false
% 0.97/1.00  
% 0.97/1.00  ------ QBF Options
% 0.97/1.00  
% 0.97/1.00  --qbf_mode                              false
% 0.97/1.00  --qbf_elim_univ                         false
% 0.97/1.00  --qbf_dom_inst                          none
% 0.97/1.00  --qbf_dom_pre_inst                      false
% 0.97/1.00  --qbf_sk_in                             false
% 0.97/1.00  --qbf_pred_elim                         true
% 0.97/1.00  --qbf_split                             512
% 0.97/1.00  
% 0.97/1.00  ------ BMC1 Options
% 0.97/1.00  
% 0.97/1.00  --bmc1_incremental                      false
% 0.97/1.00  --bmc1_axioms                           reachable_all
% 0.97/1.00  --bmc1_min_bound                        0
% 0.97/1.00  --bmc1_max_bound                        -1
% 0.97/1.00  --bmc1_max_bound_default                -1
% 0.97/1.00  --bmc1_symbol_reachability              true
% 0.97/1.00  --bmc1_property_lemmas                  false
% 0.97/1.00  --bmc1_k_induction                      false
% 0.97/1.00  --bmc1_non_equiv_states                 false
% 0.97/1.00  --bmc1_deadlock                         false
% 0.97/1.00  --bmc1_ucm                              false
% 0.97/1.00  --bmc1_add_unsat_core                   none
% 0.97/1.00  --bmc1_unsat_core_children              false
% 0.97/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.97/1.00  --bmc1_out_stat                         full
% 0.97/1.00  --bmc1_ground_init                      false
% 0.97/1.00  --bmc1_pre_inst_next_state              false
% 0.97/1.00  --bmc1_pre_inst_state                   false
% 0.97/1.00  --bmc1_pre_inst_reach_state             false
% 0.97/1.00  --bmc1_out_unsat_core                   false
% 0.97/1.00  --bmc1_aig_witness_out                  false
% 0.97/1.00  --bmc1_verbose                          false
% 0.97/1.00  --bmc1_dump_clauses_tptp                false
% 0.97/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.97/1.00  --bmc1_dump_file                        -
% 0.97/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.97/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.97/1.00  --bmc1_ucm_extend_mode                  1
% 0.97/1.00  --bmc1_ucm_init_mode                    2
% 0.97/1.00  --bmc1_ucm_cone_mode                    none
% 0.97/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.97/1.00  --bmc1_ucm_relax_model                  4
% 0.97/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.97/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.97/1.00  --bmc1_ucm_layered_model                none
% 0.97/1.00  --bmc1_ucm_max_lemma_size               10
% 0.97/1.00  
% 0.97/1.00  ------ AIG Options
% 0.97/1.00  
% 0.97/1.00  --aig_mode                              false
% 0.97/1.00  
% 0.97/1.00  ------ Instantiation Options
% 0.97/1.00  
% 0.97/1.00  --instantiation_flag                    true
% 0.97/1.00  --inst_sos_flag                         false
% 0.97/1.00  --inst_sos_phase                        true
% 0.97/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.97/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.97/1.00  --inst_lit_sel_side                     num_symb
% 0.97/1.00  --inst_solver_per_active                1400
% 0.97/1.00  --inst_solver_calls_frac                1.
% 0.97/1.00  --inst_passive_queue_type               priority_queues
% 0.97/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.97/1.00  --inst_passive_queues_freq              [25;2]
% 0.97/1.00  --inst_dismatching                      true
% 0.97/1.00  --inst_eager_unprocessed_to_passive     true
% 0.97/1.00  --inst_prop_sim_given                   true
% 0.97/1.00  --inst_prop_sim_new                     false
% 0.97/1.00  --inst_subs_new                         false
% 0.97/1.00  --inst_eq_res_simp                      false
% 0.97/1.00  --inst_subs_given                       false
% 0.97/1.00  --inst_orphan_elimination               true
% 0.97/1.00  --inst_learning_loop_flag               true
% 0.97/1.00  --inst_learning_start                   3000
% 0.97/1.00  --inst_learning_factor                  2
% 0.97/1.00  --inst_start_prop_sim_after_learn       3
% 0.97/1.00  --inst_sel_renew                        solver
% 0.97/1.00  --inst_lit_activity_flag                true
% 0.97/1.00  --inst_restr_to_given                   false
% 0.97/1.00  --inst_activity_threshold               500
% 0.97/1.00  --inst_out_proof                        true
% 0.97/1.00  
% 0.97/1.00  ------ Resolution Options
% 0.97/1.00  
% 0.97/1.00  --resolution_flag                       true
% 0.97/1.00  --res_lit_sel                           adaptive
% 0.97/1.00  --res_lit_sel_side                      none
% 0.97/1.00  --res_ordering                          kbo
% 0.97/1.00  --res_to_prop_solver                    active
% 0.97/1.00  --res_prop_simpl_new                    false
% 0.97/1.00  --res_prop_simpl_given                  true
% 0.97/1.00  --res_passive_queue_type                priority_queues
% 0.97/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.97/1.00  --res_passive_queues_freq               [15;5]
% 0.97/1.00  --res_forward_subs                      full
% 0.97/1.00  --res_backward_subs                     full
% 0.97/1.00  --res_forward_subs_resolution           true
% 0.97/1.00  --res_backward_subs_resolution          true
% 0.97/1.00  --res_orphan_elimination                true
% 0.97/1.00  --res_time_limit                        2.
% 0.97/1.00  --res_out_proof                         true
% 0.97/1.00  
% 0.97/1.00  ------ Superposition Options
% 0.97/1.00  
% 0.97/1.00  --superposition_flag                    true
% 0.97/1.00  --sup_passive_queue_type                priority_queues
% 0.97/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.97/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.97/1.00  --demod_completeness_check              fast
% 0.97/1.00  --demod_use_ground                      true
% 0.97/1.00  --sup_to_prop_solver                    passive
% 0.97/1.00  --sup_prop_simpl_new                    true
% 0.97/1.00  --sup_prop_simpl_given                  true
% 0.97/1.00  --sup_fun_splitting                     false
% 0.97/1.00  --sup_smt_interval                      50000
% 0.97/1.00  
% 0.97/1.00  ------ Superposition Simplification Setup
% 0.97/1.00  
% 0.97/1.00  --sup_indices_passive                   []
% 0.97/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.97/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/1.00  --sup_full_bw                           [BwDemod]
% 0.97/1.00  --sup_immed_triv                        [TrivRules]
% 0.97/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.97/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/1.00  --sup_immed_bw_main                     []
% 0.97/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.97/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.97/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.97/1.00  
% 0.97/1.00  ------ Combination Options
% 0.97/1.00  
% 0.97/1.00  --comb_res_mult                         3
% 0.97/1.00  --comb_sup_mult                         2
% 0.97/1.00  --comb_inst_mult                        10
% 0.97/1.00  
% 0.97/1.00  ------ Debug Options
% 0.97/1.00  
% 0.97/1.00  --dbg_backtrace                         false
% 0.97/1.00  --dbg_dump_prop_clauses                 false
% 0.97/1.00  --dbg_dump_prop_clauses_file            -
% 0.97/1.00  --dbg_out_stat                          false
% 0.97/1.00  ------ Parsing...
% 0.97/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.97/1.00  
% 0.97/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 0.97/1.00  
% 0.97/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.97/1.00  ------ Proving...
% 0.97/1.00  ------ Problem Properties 
% 0.97/1.00  
% 0.97/1.00  
% 0.97/1.00  clauses                                 10
% 0.97/1.00  conjectures                             0
% 0.97/1.00  EPR                                     2
% 0.97/1.00  Horn                                    10
% 0.97/1.00  unary                                   6
% 0.97/1.00  binary                                  0
% 0.97/1.00  lits                                    30
% 0.97/1.00  lits eq                                 0
% 0.97/1.00  fd_pure                                 0
% 0.97/1.00  fd_pseudo                               0
% 0.97/1.00  fd_cond                                 0
% 0.97/1.00  fd_pseudo_cond                          0
% 0.97/1.00  AC symbols                              0
% 0.97/1.00  
% 0.97/1.00  ------ Schedule dynamic 5 is on 
% 0.97/1.00  
% 0.97/1.00  ------ no conjectures: strip conj schedule 
% 0.97/1.00  
% 0.97/1.00  ------ no equalities: superposition off 
% 0.97/1.00  
% 0.97/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 0.97/1.00  
% 0.97/1.00  
% 0.97/1.00  ------ 
% 0.97/1.00  Current options:
% 0.97/1.00  ------ 
% 0.97/1.00  
% 0.97/1.00  ------ Input Options
% 0.97/1.00  
% 0.97/1.00  --out_options                           all
% 0.97/1.00  --tptp_safe_out                         true
% 0.97/1.00  --problem_path                          ""
% 0.97/1.00  --include_path                          ""
% 0.97/1.00  --clausifier                            res/vclausify_rel
% 0.97/1.00  --clausifier_options                    --mode clausify
% 0.97/1.00  --stdin                                 false
% 0.97/1.00  --stats_out                             all
% 0.97/1.00  
% 0.97/1.00  ------ General Options
% 0.97/1.00  
% 0.97/1.00  --fof                                   false
% 0.97/1.00  --time_out_real                         305.
% 0.97/1.00  --time_out_virtual                      -1.
% 0.97/1.00  --symbol_type_check                     false
% 0.97/1.00  --clausify_out                          false
% 0.97/1.00  --sig_cnt_out                           false
% 0.97/1.00  --trig_cnt_out                          false
% 0.97/1.00  --trig_cnt_out_tolerance                1.
% 0.97/1.00  --trig_cnt_out_sk_spl                   false
% 0.97/1.00  --abstr_cl_out                          false
% 0.97/1.00  
% 0.97/1.00  ------ Global Options
% 0.97/1.00  
% 0.97/1.00  --schedule                              default
% 0.97/1.00  --add_important_lit                     false
% 0.97/1.00  --prop_solver_per_cl                    1000
% 0.97/1.00  --min_unsat_core                        false
% 0.97/1.00  --soft_assumptions                      false
% 0.97/1.00  --soft_lemma_size                       3
% 0.97/1.00  --prop_impl_unit_size                   0
% 0.97/1.00  --prop_impl_unit                        []
% 0.97/1.00  --share_sel_clauses                     true
% 0.97/1.00  --reset_solvers                         false
% 0.97/1.00  --bc_imp_inh                            [conj_cone]
% 0.97/1.00  --conj_cone_tolerance                   3.
% 0.97/1.00  --extra_neg_conj                        none
% 0.97/1.00  --large_theory_mode                     true
% 0.97/1.00  --prolific_symb_bound                   200
% 0.97/1.00  --lt_threshold                          2000
% 0.97/1.00  --clause_weak_htbl                      true
% 0.97/1.00  --gc_record_bc_elim                     false
% 0.97/1.00  
% 0.97/1.00  ------ Preprocessing Options
% 0.97/1.00  
% 0.97/1.00  --preprocessing_flag                    true
% 0.97/1.00  --time_out_prep_mult                    0.1
% 0.97/1.00  --splitting_mode                        input
% 0.97/1.00  --splitting_grd                         true
% 0.97/1.00  --splitting_cvd                         false
% 0.97/1.00  --splitting_cvd_svl                     false
% 0.97/1.00  --splitting_nvd                         32
% 0.97/1.00  --sub_typing                            true
% 0.97/1.00  --prep_gs_sim                           true
% 0.97/1.00  --prep_unflatten                        true
% 0.97/1.00  --prep_res_sim                          true
% 0.97/1.00  --prep_upred                            true
% 0.97/1.00  --prep_sem_filter                       exhaustive
% 0.97/1.00  --prep_sem_filter_out                   false
% 0.97/1.00  --pred_elim                             true
% 0.97/1.00  --res_sim_input                         true
% 0.97/1.00  --eq_ax_congr_red                       true
% 0.97/1.00  --pure_diseq_elim                       true
% 0.97/1.00  --brand_transform                       false
% 0.97/1.00  --non_eq_to_eq                          false
% 0.97/1.00  --prep_def_merge                        true
% 0.97/1.00  --prep_def_merge_prop_impl              false
% 0.97/1.00  --prep_def_merge_mbd                    true
% 0.97/1.00  --prep_def_merge_tr_red                 false
% 0.97/1.00  --prep_def_merge_tr_cl                  false
% 0.97/1.00  --smt_preprocessing                     true
% 0.97/1.00  --smt_ac_axioms                         fast
% 0.97/1.00  --preprocessed_out                      false
% 0.97/1.00  --preprocessed_stats                    false
% 0.97/1.00  
% 0.97/1.00  ------ Abstraction refinement Options
% 0.97/1.00  
% 0.97/1.00  --abstr_ref                             []
% 0.97/1.00  --abstr_ref_prep                        false
% 0.97/1.00  --abstr_ref_until_sat                   false
% 0.97/1.00  --abstr_ref_sig_restrict                funpre
% 0.97/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.97/1.00  --abstr_ref_under                       []
% 0.97/1.00  
% 0.97/1.00  ------ SAT Options
% 0.97/1.00  
% 0.97/1.00  --sat_mode                              false
% 0.97/1.00  --sat_fm_restart_options                ""
% 0.97/1.00  --sat_gr_def                            false
% 0.97/1.00  --sat_epr_types                         true
% 0.97/1.00  --sat_non_cyclic_types                  false
% 0.97/1.00  --sat_finite_models                     false
% 0.97/1.00  --sat_fm_lemmas                         false
% 0.97/1.00  --sat_fm_prep                           false
% 0.97/1.00  --sat_fm_uc_incr                        true
% 0.97/1.00  --sat_out_model                         small
% 0.97/1.00  --sat_out_clauses                       false
% 0.97/1.00  
% 0.97/1.00  ------ QBF Options
% 0.97/1.00  
% 0.97/1.00  --qbf_mode                              false
% 0.97/1.00  --qbf_elim_univ                         false
% 0.97/1.00  --qbf_dom_inst                          none
% 0.97/1.00  --qbf_dom_pre_inst                      false
% 0.97/1.00  --qbf_sk_in                             false
% 0.97/1.00  --qbf_pred_elim                         true
% 0.97/1.00  --qbf_split                             512
% 0.97/1.00  
% 0.97/1.00  ------ BMC1 Options
% 0.97/1.00  
% 0.97/1.00  --bmc1_incremental                      false
% 0.97/1.00  --bmc1_axioms                           reachable_all
% 0.97/1.00  --bmc1_min_bound                        0
% 0.97/1.00  --bmc1_max_bound                        -1
% 0.97/1.00  --bmc1_max_bound_default                -1
% 0.97/1.00  --bmc1_symbol_reachability              true
% 0.97/1.00  --bmc1_property_lemmas                  false
% 0.97/1.00  --bmc1_k_induction                      false
% 0.97/1.00  --bmc1_non_equiv_states                 false
% 0.97/1.00  --bmc1_deadlock                         false
% 0.97/1.00  --bmc1_ucm                              false
% 0.97/1.00  --bmc1_add_unsat_core                   none
% 0.97/1.00  --bmc1_unsat_core_children              false
% 0.97/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.97/1.00  --bmc1_out_stat                         full
% 0.97/1.00  --bmc1_ground_init                      false
% 0.97/1.00  --bmc1_pre_inst_next_state              false
% 0.97/1.00  --bmc1_pre_inst_state                   false
% 0.97/1.00  --bmc1_pre_inst_reach_state             false
% 0.97/1.00  --bmc1_out_unsat_core                   false
% 0.97/1.00  --bmc1_aig_witness_out                  false
% 0.97/1.00  --bmc1_verbose                          false
% 0.97/1.00  --bmc1_dump_clauses_tptp                false
% 0.97/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.97/1.00  --bmc1_dump_file                        -
% 0.97/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.97/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.97/1.00  --bmc1_ucm_extend_mode                  1
% 0.97/1.00  --bmc1_ucm_init_mode                    2
% 0.97/1.00  --bmc1_ucm_cone_mode                    none
% 0.97/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.97/1.00  --bmc1_ucm_relax_model                  4
% 0.97/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.97/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.97/1.00  --bmc1_ucm_layered_model                none
% 0.97/1.00  --bmc1_ucm_max_lemma_size               10
% 0.97/1.00  
% 0.97/1.00  ------ AIG Options
% 0.97/1.00  
% 0.97/1.00  --aig_mode                              false
% 0.97/1.00  
% 0.97/1.00  ------ Instantiation Options
% 0.97/1.00  
% 0.97/1.00  --instantiation_flag                    true
% 0.97/1.00  --inst_sos_flag                         false
% 0.97/1.00  --inst_sos_phase                        true
% 0.97/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.97/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.97/1.00  --inst_lit_sel_side                     none
% 0.97/1.00  --inst_solver_per_active                1400
% 0.97/1.00  --inst_solver_calls_frac                1.
% 0.97/1.00  --inst_passive_queue_type               priority_queues
% 0.97/1.00  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 0.97/1.00  --inst_passive_queues_freq              [25;2]
% 0.97/1.00  --inst_dismatching                      true
% 0.97/1.00  --inst_eager_unprocessed_to_passive     true
% 0.97/1.00  --inst_prop_sim_given                   true
% 0.97/1.00  --inst_prop_sim_new                     false
% 0.97/1.00  --inst_subs_new                         false
% 0.97/1.00  --inst_eq_res_simp                      false
% 0.97/1.00  --inst_subs_given                       false
% 0.97/1.00  --inst_orphan_elimination               true
% 0.97/1.00  --inst_learning_loop_flag               true
% 0.97/1.00  --inst_learning_start                   3000
% 0.97/1.00  --inst_learning_factor                  2
% 0.97/1.00  --inst_start_prop_sim_after_learn       3
% 0.97/1.00  --inst_sel_renew                        solver
% 0.97/1.00  --inst_lit_activity_flag                true
% 0.97/1.00  --inst_restr_to_given                   false
% 0.97/1.00  --inst_activity_threshold               500
% 0.97/1.00  --inst_out_proof                        true
% 0.97/1.00  
% 0.97/1.00  ------ Resolution Options
% 0.97/1.00  
% 0.97/1.00  --resolution_flag                       false
% 0.97/1.00  --res_lit_sel                           adaptive
% 0.97/1.00  --res_lit_sel_side                      none
% 0.97/1.00  --res_ordering                          kbo
% 0.97/1.00  --res_to_prop_solver                    active
% 0.97/1.00  --res_prop_simpl_new                    false
% 0.97/1.00  --res_prop_simpl_given                  true
% 0.97/1.00  --res_passive_queue_type                priority_queues
% 0.97/1.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 0.97/1.00  --res_passive_queues_freq               [15;5]
% 0.97/1.00  --res_forward_subs                      full
% 0.97/1.00  --res_backward_subs                     full
% 0.97/1.00  --res_forward_subs_resolution           true
% 0.97/1.00  --res_backward_subs_resolution          true
% 0.97/1.00  --res_orphan_elimination                true
% 0.97/1.00  --res_time_limit                        2.
% 0.97/1.00  --res_out_proof                         true
% 0.97/1.00  
% 0.97/1.00  ------ Superposition Options
% 0.97/1.00  
% 0.97/1.00  --superposition_flag                    false
% 0.97/1.00  --sup_passive_queue_type                priority_queues
% 0.97/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.97/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.97/1.00  --demod_completeness_check              fast
% 0.97/1.00  --demod_use_ground                      true
% 0.97/1.00  --sup_to_prop_solver                    passive
% 0.97/1.00  --sup_prop_simpl_new                    true
% 0.97/1.00  --sup_prop_simpl_given                  true
% 0.97/1.00  --sup_fun_splitting                     false
% 0.97/1.00  --sup_smt_interval                      50000
% 0.97/1.00  
% 0.97/1.00  ------ Superposition Simplification Setup
% 0.97/1.00  
% 0.97/1.00  --sup_indices_passive                   []
% 0.97/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.97/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/1.00  --sup_full_bw                           [BwDemod]
% 0.97/1.00  --sup_immed_triv                        [TrivRules]
% 0.97/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.97/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/1.00  --sup_immed_bw_main                     []
% 0.97/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.97/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.97/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.97/1.00  
% 0.97/1.00  ------ Combination Options
% 0.97/1.00  
% 0.97/1.00  --comb_res_mult                         3
% 0.97/1.00  --comb_sup_mult                         2
% 0.97/1.00  --comb_inst_mult                        10
% 0.97/1.00  
% 0.97/1.00  ------ Debug Options
% 0.97/1.00  
% 0.97/1.00  --dbg_backtrace                         false
% 0.97/1.00  --dbg_dump_prop_clauses                 false
% 0.97/1.00  --dbg_dump_prop_clauses_file            -
% 0.97/1.00  --dbg_out_stat                          false
% 0.97/1.00  
% 0.97/1.00  
% 0.97/1.00  
% 0.97/1.00  
% 0.97/1.00  ------ Proving...
% 0.97/1.00  
% 0.97/1.00  
% 0.97/1.00  % SZS status Theorem for theBenchmark.p
% 0.97/1.00  
% 0.97/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 0.97/1.00  
% 0.97/1.00  fof(f6,axiom,(
% 0.97/1.00    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 0.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/1.00  
% 0.97/1.00  fof(f24,plain,(
% 0.97/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.97/1.00    inference(ennf_transformation,[],[f6])).
% 0.97/1.00  
% 0.97/1.00  fof(f25,plain,(
% 0.97/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.97/1.00    inference(flattening,[],[f24])).
% 0.97/1.00  
% 0.97/1.00  fof(f52,plain,(
% 0.97/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f25])).
% 0.97/1.00  
% 0.97/1.00  fof(f51,plain,(
% 0.97/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f25])).
% 0.97/1.00  
% 0.97/1.00  fof(f50,plain,(
% 0.97/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f25])).
% 0.97/1.00  
% 0.97/1.00  fof(f2,axiom,(
% 0.97/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/1.00  
% 0.97/1.00  fof(f18,plain,(
% 0.97/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.97/1.00    inference(ennf_transformation,[],[f2])).
% 0.97/1.00  
% 0.97/1.00  fof(f46,plain,(
% 0.97/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f18])).
% 0.97/1.00  
% 0.97/1.00  fof(f7,axiom,(
% 0.97/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/1.00  
% 0.97/1.00  fof(f14,plain,(
% 0.97/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1))))),
% 0.97/1.00    inference(pure_predicate_removal,[],[f7])).
% 0.97/1.00  
% 0.97/1.00  fof(f26,plain,(
% 0.97/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.97/1.00    inference(ennf_transformation,[],[f14])).
% 0.97/1.00  
% 0.97/1.00  fof(f27,plain,(
% 0.97/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/1.00    inference(flattening,[],[f26])).
% 0.97/1.00  
% 0.97/1.00  fof(f54,plain,(
% 0.97/1.00    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f27])).
% 0.97/1.00  
% 0.97/1.00  fof(f12,conjecture,(
% 0.97/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)))))),
% 0.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/1.00  
% 0.97/1.00  fof(f13,negated_conjecture,(
% 0.97/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)))))),
% 0.97/1.00    inference(negated_conjecture,[],[f12])).
% 0.97/1.00  
% 0.97/1.00  fof(f36,plain,(
% 0.97/1.00    ? [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.97/1.00    inference(ennf_transformation,[],[f13])).
% 0.97/1.00  
% 0.97/1.00  fof(f37,plain,(
% 0.97/1.00    ? [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.97/1.00    inference(flattening,[],[f36])).
% 0.97/1.00  
% 0.97/1.00  fof(f43,plain,(
% 0.97/1.00    ( ! [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(X0,sK2))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),sK2,k8_tmap_1(X0,sK2)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(X0,sK2))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK2))) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 0.97/1.00    introduced(choice_axiom,[])).
% 0.97/1.00  
% 0.97/1.00  fof(f42,plain,(
% 0.97/1.00    ? [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK1,X1))))) | ~v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),X1,k8_tmap_1(sK1,X1)) | ~v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK1,X1))) | ~v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X1))) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.97/1.00    introduced(choice_axiom,[])).
% 0.97/1.00  
% 0.97/1.00  fof(f44,plain,(
% 0.97/1.00    ((~m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))))) | ~v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2)) | ~v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))) | ~v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f43,f42])).
% 0.97/1.00  
% 0.97/1.00  fof(f68,plain,(
% 0.97/1.00    m1_pre_topc(sK2,sK1)),
% 0.97/1.00    inference(cnf_transformation,[],[f44])).
% 0.97/1.00  
% 0.97/1.00  fof(f64,plain,(
% 0.97/1.00    ~v2_struct_0(sK1)),
% 0.97/1.00    inference(cnf_transformation,[],[f44])).
% 0.97/1.00  
% 0.97/1.00  fof(f65,plain,(
% 0.97/1.00    v2_pre_topc(sK1)),
% 0.97/1.00    inference(cnf_transformation,[],[f44])).
% 0.97/1.00  
% 0.97/1.00  fof(f66,plain,(
% 0.97/1.00    l1_pre_topc(sK1)),
% 0.97/1.00    inference(cnf_transformation,[],[f44])).
% 0.97/1.00  
% 0.97/1.00  fof(f11,axiom,(
% 0.97/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 0.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/1.00  
% 0.97/1.00  fof(f34,plain,(
% 0.97/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.97/1.00    inference(ennf_transformation,[],[f11])).
% 0.97/1.00  
% 0.97/1.00  fof(f35,plain,(
% 0.97/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/1.00    inference(flattening,[],[f34])).
% 0.97/1.00  
% 0.97/1.00  fof(f38,plain,(
% 0.97/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/1.00    inference(nnf_transformation,[],[f35])).
% 0.97/1.00  
% 0.97/1.00  fof(f39,plain,(
% 0.97/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/1.00    inference(rectify,[],[f38])).
% 0.97/1.00  
% 0.97/1.00  fof(f40,plain,(
% 0.97/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_tmap_1(X1,X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1))))),
% 0.97/1.00    introduced(choice_axiom,[])).
% 0.97/1.00  
% 0.97/1.00  fof(f41,plain,(
% 0.97/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | (~r1_tmap_1(X1,X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 0.97/1.00  
% 0.97/1.00  fof(f62,plain,(
% 0.97/1.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X1,X0) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f41])).
% 0.97/1.00  
% 0.97/1.00  fof(f69,plain,(
% 0.97/1.00    ~m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))))) | ~v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2)) | ~v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2))) | ~v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))),
% 0.97/1.00    inference(cnf_transformation,[],[f44])).
% 0.97/1.00  
% 0.97/1.00  fof(f67,plain,(
% 0.97/1.00    ~v2_struct_0(sK2)),
% 0.97/1.00    inference(cnf_transformation,[],[f44])).
% 0.97/1.00  
% 0.97/1.00  fof(f9,axiom,(
% 0.97/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))))),
% 0.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/1.00  
% 0.97/1.00  fof(f15,plain,(
% 0.97/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))))),
% 0.97/1.00    inference(pure_predicate_removal,[],[f9])).
% 0.97/1.00  
% 0.97/1.00  fof(f30,plain,(
% 0.97/1.00    ! [X0,X1] : ((v2_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.97/1.00    inference(ennf_transformation,[],[f15])).
% 0.97/1.00  
% 0.97/1.00  fof(f31,plain,(
% 0.97/1.00    ! [X0,X1] : ((v2_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/1.00    inference(flattening,[],[f30])).
% 0.97/1.00  
% 0.97/1.00  fof(f58,plain,(
% 0.97/1.00    ( ! [X0,X1] : (~v2_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f31])).
% 0.97/1.00  
% 0.97/1.00  fof(f53,plain,(
% 0.97/1.00    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f27])).
% 0.97/1.00  
% 0.97/1.00  fof(f3,axiom,(
% 0.97/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/1.00  
% 0.97/1.00  fof(f19,plain,(
% 0.97/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.97/1.00    inference(ennf_transformation,[],[f3])).
% 0.97/1.00  
% 0.97/1.00  fof(f47,plain,(
% 0.97/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f19])).
% 0.97/1.00  
% 0.97/1.00  fof(f1,axiom,(
% 0.97/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/1.00  
% 0.97/1.00  fof(f16,plain,(
% 0.97/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.97/1.00    inference(ennf_transformation,[],[f1])).
% 0.97/1.00  
% 0.97/1.00  fof(f17,plain,(
% 0.97/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.97/1.00    inference(flattening,[],[f16])).
% 0.97/1.00  
% 0.97/1.00  fof(f45,plain,(
% 0.97/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f17])).
% 0.97/1.00  
% 0.97/1.00  fof(f63,plain,(
% 0.97/1.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X1,X0) | ~r1_tmap_1(X1,X0,X2,sK0(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f41])).
% 0.97/1.00  
% 0.97/1.00  fof(f10,axiom,(
% 0.97/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 0.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/1.00  
% 0.97/1.00  fof(f32,plain,(
% 0.97/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.97/1.00    inference(ennf_transformation,[],[f10])).
% 0.97/1.00  
% 0.97/1.00  fof(f33,plain,(
% 0.97/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/1.00    inference(flattening,[],[f32])).
% 0.97/1.00  
% 0.97/1.00  fof(f60,plain,(
% 0.97/1.00    ( ! [X2,X0,X1] : (r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f33])).
% 0.97/1.00  
% 0.97/1.00  fof(f8,axiom,(
% 0.97/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 0.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/1.00  
% 0.97/1.00  fof(f28,plain,(
% 0.97/1.00    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.97/1.00    inference(ennf_transformation,[],[f8])).
% 0.97/1.00  
% 0.97/1.00  fof(f29,plain,(
% 0.97/1.00    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/1.00    inference(flattening,[],[f28])).
% 0.97/1.00  
% 0.97/1.00  fof(f57,plain,(
% 0.97/1.00    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f29])).
% 0.97/1.00  
% 0.97/1.00  fof(f56,plain,(
% 0.97/1.00    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f29])).
% 0.97/1.00  
% 0.97/1.00  fof(f55,plain,(
% 0.97/1.00    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/1.00    inference(cnf_transformation,[],[f29])).
% 0.97/1.00  
% 0.97/1.00  cnf(c_5,plain,
% 0.97/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 0.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 0.97/1.00      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 0.97/1.00      | ~ v1_funct_1(X0)
% 0.97/1.00      | ~ l1_struct_0(X1)
% 0.97/1.00      | ~ l1_struct_0(X2)
% 0.97/1.00      | ~ l1_struct_0(X3) ),
% 0.97/1.00      inference(cnf_transformation,[],[f52]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_507,plain,
% 0.97/1.00      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 0.97/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 0.97/1.00      | m1_subset_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
% 0.97/1.00      | ~ v1_funct_1(X0_49)
% 0.97/1.00      | ~ l1_struct_0(X1_48)
% 0.97/1.00      | ~ l1_struct_0(X2_48)
% 0.97/1.00      | ~ l1_struct_0(X0_48) ),
% 0.97/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_564,plain,
% 0.97/1.00      ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(X0_48),u1_struct_0(X1_48))
% 0.97/1.00      | m1_subset_1(k2_tmap_1(X0_48,X1_48,k9_tmap_1(sK1,sK2),X2_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
% 0.97/1.00      | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 0.97/1.00      | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_struct_0(X1_48)
% 0.97/1.00      | ~ l1_struct_0(X2_48)
% 0.97/1.00      | ~ l1_struct_0(X0_48) ),
% 0.97/1.00      inference(instantiation,[status(thm)],[c_507]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_636,plain,
% 0.97/1.00      ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 0.97/1.00      | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 0.97/1.00      | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 0.97/1.00      | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_struct_0(X0_48)
% 0.97/1.00      | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_struct_0(sK1) ),
% 0.97/1.00      inference(instantiation,[status(thm)],[c_564]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_638,plain,
% 0.97/1.00      ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 0.97/1.00      | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 0.97/1.00      | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 0.97/1.00      | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_struct_0(sK2)
% 0.97/1.00      | ~ l1_struct_0(sK1) ),
% 0.97/1.00      inference(instantiation,[status(thm)],[c_636]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_6,plain,
% 0.97/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 0.97/1.00      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 0.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 0.97/1.00      | ~ v1_funct_1(X0)
% 0.97/1.00      | ~ l1_struct_0(X1)
% 0.97/1.00      | ~ l1_struct_0(X2)
% 0.97/1.00      | ~ l1_struct_0(X3) ),
% 0.97/1.00      inference(cnf_transformation,[],[f51]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_506,plain,
% 0.97/1.00      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 0.97/1.00      | v1_funct_2(k2_tmap_1(X0_48,X1_48,X0_49,X2_48),u1_struct_0(X2_48),u1_struct_0(X1_48))
% 0.97/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 0.97/1.00      | ~ v1_funct_1(X0_49)
% 0.97/1.00      | ~ l1_struct_0(X1_48)
% 0.97/1.00      | ~ l1_struct_0(X2_48)
% 0.97/1.00      | ~ l1_struct_0(X0_48) ),
% 0.97/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_559,plain,
% 0.97/1.00      ( v1_funct_2(k2_tmap_1(X0_48,X1_48,k9_tmap_1(sK1,sK2),X2_48),u1_struct_0(X2_48),u1_struct_0(X1_48))
% 0.97/1.00      | ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(X0_48),u1_struct_0(X1_48))
% 0.97/1.00      | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 0.97/1.00      | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_struct_0(X1_48)
% 0.97/1.00      | ~ l1_struct_0(X2_48)
% 0.97/1.00      | ~ l1_struct_0(X0_48) ),
% 0.97/1.00      inference(instantiation,[status(thm)],[c_506]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_590,plain,
% 0.97/1.00      ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),X0_48),u1_struct_0(X0_48),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 0.97/1.00      | ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 0.97/1.00      | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 0.97/1.00      | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_struct_0(X0_48)
% 0.97/1.00      | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_struct_0(sK1) ),
% 0.97/1.00      inference(instantiation,[status(thm)],[c_559]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_592,plain,
% 0.97/1.00      ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 0.97/1.00      | ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 0.97/1.00      | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 0.97/1.00      | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_struct_0(sK2)
% 0.97/1.00      | ~ l1_struct_0(sK1) ),
% 0.97/1.00      inference(instantiation,[status(thm)],[c_590]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_7,plain,
% 0.97/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 0.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 0.97/1.00      | ~ v1_funct_1(X0)
% 0.97/1.00      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3))
% 0.97/1.00      | ~ l1_struct_0(X1)
% 0.97/1.00      | ~ l1_struct_0(X2)
% 0.97/1.00      | ~ l1_struct_0(X3) ),
% 0.97/1.00      inference(cnf_transformation,[],[f50]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_505,plain,
% 0.97/1.00      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 0.97/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 0.97/1.00      | ~ v1_funct_1(X0_49)
% 0.97/1.00      | v1_funct_1(k2_tmap_1(X0_48,X1_48,X0_49,X2_48))
% 0.97/1.00      | ~ l1_struct_0(X1_48)
% 0.97/1.00      | ~ l1_struct_0(X2_48)
% 0.97/1.00      | ~ l1_struct_0(X0_48) ),
% 0.97/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_554,plain,
% 0.97/1.00      ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(X0_48),u1_struct_0(X1_48))
% 0.97/1.00      | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 0.97/1.00      | v1_funct_1(k2_tmap_1(X0_48,X1_48,k9_tmap_1(sK1,sK2),X2_48))
% 0.97/1.00      | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_struct_0(X1_48)
% 0.97/1.00      | ~ l1_struct_0(X2_48)
% 0.97/1.00      | ~ l1_struct_0(X0_48) ),
% 0.97/1.00      inference(instantiation,[status(thm)],[c_505]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_569,plain,
% 0.97/1.00      ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 0.97/1.00      | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 0.97/1.00      | v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
% 0.97/1.00      | ~ v1_funct_1(k9_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_struct_0(sK2)
% 0.97/1.00      | ~ l1_struct_0(sK1) ),
% 0.97/1.00      inference(instantiation,[status(thm)],[c_554]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_1,plain,
% 0.97/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 0.97/1.00      inference(cnf_transformation,[],[f46]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_8,plain,
% 0.97/1.00      ( ~ m1_pre_topc(X0,X1)
% 0.97/1.00      | v2_struct_0(X1)
% 0.97/1.00      | ~ l1_pre_topc(X1)
% 0.97/1.00      | l1_pre_topc(k8_tmap_1(X1,X0))
% 0.97/1.00      | ~ v2_pre_topc(X1) ),
% 0.97/1.00      inference(cnf_transformation,[],[f54]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_20,negated_conjecture,
% 0.97/1.00      ( m1_pre_topc(sK2,sK1) ),
% 0.97/1.00      inference(cnf_transformation,[],[f68]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_300,plain,
% 0.97/1.00      ( v2_struct_0(sK1)
% 0.97/1.00      | l1_pre_topc(k8_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_pre_topc(sK1)
% 0.97/1.00      | ~ v2_pre_topc(sK1) ),
% 0.97/1.00      inference(resolution,[status(thm)],[c_8,c_20]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_24,negated_conjecture,
% 0.97/1.00      ( ~ v2_struct_0(sK1) ),
% 0.97/1.00      inference(cnf_transformation,[],[f64]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_23,negated_conjecture,
% 0.97/1.00      ( v2_pre_topc(sK1) ),
% 0.97/1.00      inference(cnf_transformation,[],[f65]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_22,negated_conjecture,
% 0.97/1.00      ( l1_pre_topc(sK1) ),
% 0.97/1.00      inference(cnf_transformation,[],[f66]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_302,plain,
% 0.97/1.00      ( l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 0.97/1.00      inference(global_propositional_subsumption,
% 0.97/1.00                [status(thm)],
% 0.97/1.00                [c_300,c_24,c_23,c_22]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_426,plain,
% 0.97/1.00      ( l1_struct_0(k8_tmap_1(sK1,sK2)) ),
% 0.97/1.00      inference(resolution,[status(thm)],[c_1,c_302]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_414,plain,
% 0.97/1.00      ( l1_struct_0(sK1) ),
% 0.97/1.00      inference(resolution,[status(thm)],[c_1,c_22]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_17,plain,
% 0.97/1.00      ( v5_pre_topc(X0,X1,X2)
% 0.97/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 0.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 0.97/1.00      | m1_subset_1(sK0(X2,X1,X0),u1_struct_0(X1))
% 0.97/1.00      | ~ v1_funct_1(X0)
% 0.97/1.00      | v2_struct_0(X2)
% 0.97/1.00      | v2_struct_0(X1)
% 0.97/1.00      | ~ l1_pre_topc(X2)
% 0.97/1.00      | ~ l1_pre_topc(X1)
% 0.97/1.00      | ~ v2_pre_topc(X2)
% 0.97/1.00      | ~ v2_pre_topc(X1) ),
% 0.97/1.00      inference(cnf_transformation,[],[f62]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_19,negated_conjecture,
% 0.97/1.00      ( ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 0.97/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 0.97/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
% 0.97/1.00      inference(cnf_transformation,[],[f69]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_394,plain,
% 0.97/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 0.97/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 0.97/1.00      | m1_subset_1(sK0(k8_tmap_1(sK1,sK2),sK2,k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)),u1_struct_0(sK2))
% 0.97/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
% 0.97/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 0.97/1.00      | v2_struct_0(sK2)
% 0.97/1.00      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_pre_topc(sK2)
% 0.97/1.00      | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ v2_pre_topc(sK2) ),
% 0.97/1.00      inference(resolution,[status(thm)],[c_17,c_19]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_21,negated_conjecture,
% 0.97/1.00      ( ~ v2_struct_0(sK2) ),
% 0.97/1.00      inference(cnf_transformation,[],[f67]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_14,plain,
% 0.97/1.00      ( ~ m1_pre_topc(X0,X1)
% 0.97/1.00      | v2_struct_0(X1)
% 0.97/1.00      | ~ v2_struct_0(k8_tmap_1(X1,X0))
% 0.97/1.00      | ~ l1_pre_topc(X1)
% 0.97/1.00      | ~ v2_pre_topc(X1) ),
% 0.97/1.00      inference(cnf_transformation,[],[f58]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_270,plain,
% 0.97/1.00      ( ~ v2_struct_0(k8_tmap_1(sK1,sK2))
% 0.97/1.00      | v2_struct_0(sK1)
% 0.97/1.00      | ~ l1_pre_topc(sK1)
% 0.97/1.00      | ~ v2_pre_topc(sK1) ),
% 0.97/1.00      inference(resolution,[status(thm)],[c_14,c_20]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_9,plain,
% 0.97/1.00      ( ~ m1_pre_topc(X0,X1)
% 0.97/1.00      | v2_struct_0(X1)
% 0.97/1.00      | ~ l1_pre_topc(X1)
% 0.97/1.00      | ~ v2_pre_topc(X1)
% 0.97/1.00      | v2_pre_topc(k8_tmap_1(X1,X0)) ),
% 0.97/1.00      inference(cnf_transformation,[],[f53]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_290,plain,
% 0.97/1.00      ( v2_struct_0(sK1)
% 0.97/1.00      | ~ l1_pre_topc(sK1)
% 0.97/1.00      | v2_pre_topc(k8_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ v2_pre_topc(sK1) ),
% 0.97/1.00      inference(resolution,[status(thm)],[c_9,c_20]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_2,plain,
% 0.97/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 0.97/1.00      inference(cnf_transformation,[],[f47]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_310,plain,
% 0.97/1.00      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 0.97/1.00      inference(resolution,[status(thm)],[c_2,c_20]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_0,plain,
% 0.97/1.00      ( ~ m1_pre_topc(X0,X1)
% 0.97/1.00      | ~ l1_pre_topc(X1)
% 0.97/1.00      | ~ v2_pre_topc(X1)
% 0.97/1.00      | v2_pre_topc(X0) ),
% 0.97/1.00      inference(cnf_transformation,[],[f45]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_320,plain,
% 0.97/1.00      ( ~ l1_pre_topc(sK1) | v2_pre_topc(sK2) | ~ v2_pre_topc(sK1) ),
% 0.97/1.00      inference(resolution,[status(thm)],[c_0,c_20]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_16,plain,
% 0.97/1.00      ( ~ r1_tmap_1(X0,X1,X2,sK0(X1,X0,X2))
% 0.97/1.00      | v5_pre_topc(X2,X0,X1)
% 0.97/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 0.97/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 0.97/1.00      | ~ v1_funct_1(X2)
% 0.97/1.00      | v2_struct_0(X1)
% 0.97/1.00      | v2_struct_0(X0)
% 0.97/1.00      | ~ l1_pre_topc(X1)
% 0.97/1.00      | ~ l1_pre_topc(X0)
% 0.97/1.00      | ~ v2_pre_topc(X1)
% 0.97/1.00      | ~ v2_pre_topc(X0) ),
% 0.97/1.00      inference(cnf_transformation,[],[f63]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_15,plain,
% 0.97/1.00      ( r1_tmap_1(X0,k8_tmap_1(X1,X0),k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),X0),X2)
% 0.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.97/1.00      | ~ m1_pre_topc(X0,X1)
% 0.97/1.00      | v2_struct_0(X1)
% 0.97/1.00      | v2_struct_0(X0)
% 0.97/1.00      | ~ l1_pre_topc(X1)
% 0.97/1.00      | ~ v2_pre_topc(X1) ),
% 0.97/1.00      inference(cnf_transformation,[],[f60]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_253,plain,
% 0.97/1.00      ( r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),X0)
% 0.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 0.97/1.00      | v2_struct_0(sK2)
% 0.97/1.00      | v2_struct_0(sK1)
% 0.97/1.00      | ~ l1_pre_topc(sK1)
% 0.97/1.00      | ~ v2_pre_topc(sK1) ),
% 0.97/1.00      inference(resolution,[status(thm)],[c_15,c_20]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_257,plain,
% 0.97/1.00      ( r1_tmap_1(sK2,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),X0)
% 0.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 0.97/1.00      inference(global_propositional_subsumption,
% 0.97/1.00                [status(thm)],
% 0.97/1.00                [c_253,c_24,c_23,c_22,c_21]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_370,plain,
% 0.97/1.00      ( v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),sK2,k8_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 0.97/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 0.97/1.00      | ~ m1_subset_1(sK0(k8_tmap_1(sK1,sK2),sK2,k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)),u1_struct_0(sK2))
% 0.97/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2))
% 0.97/1.00      | v2_struct_0(k8_tmap_1(sK1,sK2))
% 0.97/1.00      | v2_struct_0(sK2)
% 0.97/1.00      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ l1_pre_topc(sK2)
% 0.97/1.00      | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
% 0.97/1.00      | ~ v2_pre_topc(sK2) ),
% 0.97/1.00      inference(resolution,[status(thm)],[c_16,c_257]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_372,plain,
% 0.97/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 0.97/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 0.97/1.00      | ~ m1_subset_1(sK0(k8_tmap_1(sK1,sK2),sK2,k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)),u1_struct_0(sK2))
% 0.97/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
% 0.97/1.00      inference(global_propositional_subsumption,
% 0.97/1.00                [status(thm)],
% 0.97/1.00                [c_370,c_24,c_23,c_22,c_21,c_19,c_270,c_290,c_300,c_310,
% 0.97/1.00                 c_320]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_396,plain,
% 0.97/1.00      ( ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 0.97/1.00      | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 0.97/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
% 0.97/1.00      inference(global_propositional_subsumption,
% 0.97/1.00                [status(thm)],
% 0.97/1.00                [c_394,c_24,c_23,c_22,c_21,c_270,c_290,c_300,c_310,c_320,
% 0.97/1.00                 c_372]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_397,plain,
% 0.97/1.00      ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 0.97/1.00      | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 0.97/1.00      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK2)) ),
% 0.97/1.00      inference(renaming,[status(thm)],[c_396]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_10,plain,
% 0.97/1.00      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 0.97/1.00      | ~ m1_pre_topc(X1,X0)
% 0.97/1.00      | v2_struct_0(X0)
% 0.97/1.00      | ~ l1_pre_topc(X0)
% 0.97/1.00      | ~ v2_pre_topc(X0) ),
% 0.97/1.00      inference(cnf_transformation,[],[f57]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_340,plain,
% 0.97/1.00      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 0.97/1.00      | v2_struct_0(sK1)
% 0.97/1.00      | ~ l1_pre_topc(sK1)
% 0.97/1.00      | ~ v2_pre_topc(sK1) ),
% 0.97/1.00      inference(resolution,[status(thm)],[c_10,c_20]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_11,plain,
% 0.97/1.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 0.97/1.00      | ~ m1_pre_topc(X1,X0)
% 0.97/1.00      | v2_struct_0(X0)
% 0.97/1.00      | ~ l1_pre_topc(X0)
% 0.97/1.00      | ~ v2_pre_topc(X0) ),
% 0.97/1.00      inference(cnf_transformation,[],[f56]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_330,plain,
% 0.97/1.00      ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 0.97/1.00      | v2_struct_0(sK1)
% 0.97/1.00      | ~ l1_pre_topc(sK1)
% 0.97/1.00      | ~ v2_pre_topc(sK1) ),
% 0.97/1.00      inference(resolution,[status(thm)],[c_11,c_20]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_12,plain,
% 0.97/1.00      ( ~ m1_pre_topc(X0,X1)
% 0.97/1.00      | v1_funct_1(k9_tmap_1(X1,X0))
% 0.97/1.00      | v2_struct_0(X1)
% 0.97/1.00      | ~ l1_pre_topc(X1)
% 0.97/1.00      | ~ v2_pre_topc(X1) ),
% 0.97/1.00      inference(cnf_transformation,[],[f55]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_280,plain,
% 0.97/1.00      ( v1_funct_1(k9_tmap_1(sK1,sK2))
% 0.97/1.00      | v2_struct_0(sK1)
% 0.97/1.00      | ~ l1_pre_topc(sK1)
% 0.97/1.00      | ~ v2_pre_topc(sK1) ),
% 0.97/1.00      inference(resolution,[status(thm)],[c_12,c_20]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(c_77,plain,
% 0.97/1.00      ( l1_struct_0(sK2) | ~ l1_pre_topc(sK2) ),
% 0.97/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 0.97/1.00  
% 0.97/1.00  cnf(contradiction,plain,
% 0.97/1.00      ( $false ),
% 0.97/1.00      inference(minisat,
% 0.97/1.00                [status(thm)],
% 0.97/1.00                [c_638,c_592,c_569,c_426,c_414,c_397,c_340,c_330,c_310,
% 0.97/1.00                 c_280,c_77,c_22,c_23,c_24]) ).
% 0.97/1.00  
% 0.97/1.00  
% 0.97/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 0.97/1.00  
% 0.97/1.00  ------                               Statistics
% 0.97/1.00  
% 0.97/1.00  ------ General
% 0.97/1.00  
% 0.97/1.00  abstr_ref_over_cycles:                  0
% 0.97/1.00  abstr_ref_under_cycles:                 0
% 0.97/1.00  gc_basic_clause_elim:                   0
% 0.97/1.00  forced_gc_time:                         0
% 0.97/1.00  parsing_time:                           0.02
% 0.97/1.00  unif_index_cands_time:                  0.
% 0.97/1.00  unif_index_add_time:                    0.
% 0.97/1.00  orderings_time:                         0.
% 0.97/1.00  out_proof_time:                         0.009
% 0.97/1.00  total_time:                             0.067
% 0.97/1.00  num_of_symbols:                         56
% 0.97/1.00  num_of_terms:                           814
% 0.97/1.00  
% 0.97/1.00  ------ Preprocessing
% 0.97/1.00  
% 0.97/1.00  num_of_splits:                          0
% 0.97/1.00  num_of_split_atoms:                     0
% 0.97/1.00  num_of_reused_defs:                     0
% 0.97/1.00  num_eq_ax_congr_red:                    0
% 0.97/1.00  num_of_sem_filtered_clauses:            0
% 0.97/1.00  num_of_subtypes:                        5
% 0.97/1.00  monotx_restored_types:                  0
% 0.97/1.00  sat_num_of_epr_types:                   0
% 0.97/1.00  sat_num_of_non_cyclic_types:            0
% 0.97/1.00  sat_guarded_non_collapsed_types:        0
% 0.97/1.00  num_pure_diseq_elim:                    0
% 0.97/1.00  simp_replaced_by:                       0
% 0.97/1.00  res_preprocessed:                       34
% 0.97/1.00  prep_upred:                             0
% 0.97/1.00  prep_unflattend:                        0
% 0.97/1.00  smt_new_axioms:                         0
% 0.97/1.00  pred_elim_cands:                        4
% 0.97/1.00  pred_elim:                              7
% 0.97/1.00  pred_elim_cl:                           14
% 0.97/1.00  pred_elim_cycles:                       9
% 0.97/1.00  merged_defs:                            0
% 0.97/1.00  merged_defs_ncl:                        0
% 0.97/1.00  bin_hyper_res:                          0
% 0.97/1.00  prep_cycles:                            2
% 0.97/1.00  pred_elim_time:                         0.005
% 0.97/1.00  splitting_time:                         0.
% 0.97/1.00  sem_filter_time:                        0.
% 0.97/1.00  monotx_time:                            0.
% 0.97/1.00  subtype_inf_time:                       0.
% 0.97/1.00  
% 0.97/1.00  ------ Problem properties
% 0.97/1.00  
% 0.97/1.00  clauses:                                10
% 0.97/1.00  conjectures:                            0
% 0.97/1.00  epr:                                    2
% 0.97/1.00  horn:                                   10
% 0.97/1.00  ground:                                 7
% 0.97/1.00  unary:                                  6
% 0.97/1.00  binary:                                 0
% 0.97/1.00  lits:                                   30
% 0.97/1.00  lits_eq:                                0
% 0.97/1.00  fd_pure:                                0
% 0.97/1.00  fd_pseudo:                              0
% 0.97/1.00  fd_cond:                                0
% 0.97/1.00  fd_pseudo_cond:                         0
% 0.97/1.00  ac_symbols:                             0
% 0.97/1.00  
% 0.97/1.00  ------ Propositional Solver
% 0.97/1.00  
% 0.97/1.00  prop_solver_calls:                      14
% 0.97/1.00  prop_fast_solver_calls:                 373
% 0.97/1.00  smt_solver_calls:                       0
% 0.97/1.00  smt_fast_solver_calls:                  0
% 0.97/1.00  prop_num_of_clauses:                    195
% 0.97/1.00  prop_preprocess_simplified:             1044
% 0.97/1.00  prop_fo_subsumed:                       39
% 0.97/1.00  prop_solver_time:                       0.
% 0.97/1.00  smt_solver_time:                        0.
% 0.97/1.00  smt_fast_solver_time:                   0.
% 0.97/1.00  prop_fast_solver_time:                  0.
% 0.97/1.00  prop_unsat_core_time:                   0.
% 0.97/1.00  
% 0.97/1.00  ------ QBF
% 0.97/1.00  
% 0.97/1.00  qbf_q_res:                              0
% 0.97/1.00  qbf_num_tautologies:                    0
% 0.97/1.00  qbf_prep_cycles:                        0
% 0.97/1.00  
% 0.97/1.00  ------ BMC1
% 0.97/1.00  
% 0.97/1.00  bmc1_current_bound:                     -1
% 0.97/1.00  bmc1_last_solved_bound:                 -1
% 0.97/1.00  bmc1_unsat_core_size:                   -1
% 0.97/1.00  bmc1_unsat_core_parents_size:           -1
% 0.97/1.00  bmc1_merge_next_fun:                    0
% 0.97/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.97/1.00  
% 0.97/1.00  ------ Instantiation
% 0.97/1.00  
% 0.97/1.00  inst_num_of_clauses:                    27
% 0.97/1.00  inst_num_in_passive:                    2
% 0.97/1.00  inst_num_in_active:                     19
% 0.97/1.00  inst_num_in_unprocessed:                5
% 0.97/1.00  inst_num_of_loops:                      27
% 0.97/1.00  inst_num_of_learning_restarts:          0
% 0.97/1.00  inst_num_moves_active_passive:          5
% 0.97/1.00  inst_lit_activity:                      0
% 0.97/1.00  inst_lit_activity_moves:                0
% 0.97/1.00  inst_num_tautologies:                   0
% 0.97/1.00  inst_num_prop_implied:                  0
% 0.97/1.00  inst_num_existing_simplified:           0
% 0.97/1.00  inst_num_eq_res_simplified:             0
% 0.97/1.00  inst_num_child_elim:                    0
% 0.97/1.00  inst_num_of_dismatching_blockings:      6
% 0.97/1.00  inst_num_of_non_proper_insts:           15
% 0.97/1.00  inst_num_of_duplicates:                 0
% 0.97/1.00  inst_inst_num_from_inst_to_res:         0
% 0.97/1.00  inst_dismatching_checking_time:         0.
% 0.97/1.00  
% 0.97/1.00  ------ Resolution
% 0.97/1.00  
% 0.97/1.00  res_num_of_clauses:                     0
% 0.97/1.00  res_num_in_passive:                     0
% 0.97/1.00  res_num_in_active:                      0
% 0.97/1.00  res_num_of_loops:                       36
% 0.97/1.00  res_forward_subset_subsumed:            0
% 0.97/1.00  res_backward_subset_subsumed:           0
% 0.97/1.00  res_forward_subsumed:                   0
% 0.97/1.00  res_backward_subsumed:                  1
% 0.97/1.00  res_forward_subsumption_resolution:     0
% 0.97/1.00  res_backward_subsumption_resolution:    0
% 0.97/1.00  res_clause_to_clause_subsumption:       1
% 0.97/1.00  res_orphan_elimination:                 0
% 0.97/1.00  res_tautology_del:                      2
% 0.97/1.00  res_num_eq_res_simplified:              0
% 0.97/1.00  res_num_sel_changes:                    0
% 0.97/1.00  res_moves_from_active_to_pass:          0
% 0.97/1.00  
% 0.97/1.00  ------ Superposition
% 0.97/1.00  
% 0.97/1.00  sup_time_total:                         0.
% 0.97/1.00  sup_time_generating:                    0.
% 0.97/1.00  sup_time_sim_full:                      0.
% 0.97/1.00  sup_time_sim_immed:                     0.
% 0.97/1.00  
% 0.97/1.00  sup_num_of_clauses:                     0
% 0.97/1.00  sup_num_in_active:                      0
% 0.97/1.00  sup_num_in_passive:                     0
% 0.97/1.00  sup_num_of_loops:                       0
% 0.97/1.00  sup_fw_superposition:                   0
% 0.97/1.00  sup_bw_superposition:                   0
% 0.97/1.00  sup_immediate_simplified:               0
% 0.97/1.00  sup_given_eliminated:                   0
% 0.97/1.00  comparisons_done:                       0
% 0.97/1.00  comparisons_avoided:                    0
% 0.97/1.00  
% 0.97/1.00  ------ Simplifications
% 0.97/1.00  
% 0.97/1.00  
% 0.97/1.00  sim_fw_subset_subsumed:                 0
% 0.97/1.00  sim_bw_subset_subsumed:                 0
% 0.97/1.00  sim_fw_subsumed:                        0
% 0.97/1.00  sim_bw_subsumed:                        0
% 0.97/1.00  sim_fw_subsumption_res:                 0
% 0.97/1.00  sim_bw_subsumption_res:                 0
% 0.97/1.00  sim_tautology_del:                      0
% 0.97/1.00  sim_eq_tautology_del:                   0
% 0.97/1.00  sim_eq_res_simp:                        0
% 0.97/1.00  sim_fw_demodulated:                     0
% 0.97/1.00  sim_bw_demodulated:                     0
% 0.97/1.00  sim_light_normalised:                   0
% 0.97/1.00  sim_joinable_taut:                      0
% 0.97/1.00  sim_joinable_simp:                      0
% 0.97/1.00  sim_ac_normalised:                      0
% 0.97/1.00  sim_smt_subsumption:                    0
% 0.97/1.00  
%------------------------------------------------------------------------------
