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
% DateTime   : Thu Dec  3 12:24:00 EST 2020

% Result     : Theorem 27.71s
% Output     : CNFRefutation 27.71s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_37013)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_subset_1(k7_tmap_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2)))))
          | ~ v5_pre_topc(k7_tmap_1(X0,sK2),X0,k6_tmap_1(X0,sK2))
          | ~ v1_funct_2(k7_tmap_1(X0,sK2),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2)))
          | ~ v1_funct_1(k7_tmap_1(X0,sK2))
          | ~ v3_pre_topc(sK2,X0) )
        & ( ( m1_subset_1(k7_tmap_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2)))))
            & v5_pre_topc(k7_tmap_1(X0,sK2),X0,k6_tmap_1(X0,sK2))
            & v1_funct_2(k7_tmap_1(X0,sK2),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2)))
            & v1_funct_1(k7_tmap_1(X0,sK2)) )
          | v3_pre_topc(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              | ~ v1_funct_1(k7_tmap_1(X0,X1))
              | ~ v3_pre_topc(X1,X0) )
            & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) )
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(sK1,X1),sK1,k6_tmap_1(sK1,X1))
            | ~ v1_funct_2(k7_tmap_1(sK1,X1),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1)))
            | ~ v1_funct_1(k7_tmap_1(sK1,X1))
            | ~ v3_pre_topc(X1,sK1) )
          & ( ( m1_subset_1(k7_tmap_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1)))))
              & v5_pre_topc(k7_tmap_1(sK1,X1),sK1,k6_tmap_1(sK1,X1))
              & v1_funct_2(k7_tmap_1(sK1,X1),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1)))
              & v1_funct_1(k7_tmap_1(sK1,X1)) )
            | v3_pre_topc(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
      | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
      | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
      | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
      | ~ v3_pre_topc(sK2,sK1) )
    & ( ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
        & v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
        & v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
        & v1_funct_1(k7_tmap_1(sK1,sK2)) )
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f45,f44])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
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
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f38,plain,(
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
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v3_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
                    & v3_pre_topc(sK0(X0,X1,X2),X1)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
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
    inference(equality_resolution,[],[f50])).

fof(f76,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v3_pre_topc(sK0(X0,X1,X2),X1)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v3_pre_topc(sK0(X0,X1,X2),X1)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2473,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_3408,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2473])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k8_relset_1(X1,X1,k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2489,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X0_54))
    | k8_relset_1(X0_54,X0_54,k6_partfun1(X0_54),X0_52) = X0_52 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3392,plain,
    ( k8_relset_1(X0_54,X0_54,k6_partfun1(X0_54),X0_52) = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2489])).

cnf(c_3522,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_3408,c_3392])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_467,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_31,c_30])).

cnf(c_2465,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0_52)) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_472])).

cnf(c_3416,plain,
    ( u1_struct_0(k6_tmap_1(sK1,X0_52)) = u1_struct_0(sK1)
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2465])).

cnf(c_5246,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_3408,c_3416])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2479,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v5_pre_topc(X0_52,X0_55,X1_55)
    | ~ v3_pre_topc(X1_52,X1_55)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_52,X1_52),X0_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | k2_struct_0(X1_55) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3402,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_52,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_52,X1_55,X0_55) != iProver_top
    | v3_pre_topc(X1_52,X0_55) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X0_55),X0_52,X1_52),X1_55) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2479])).

cnf(c_5413,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_52,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_52,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_52,X1_52),X0_55) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5246,c_3402])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | l1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_562,plain,
    ( l1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_31,c_30])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | l1_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_562])).

cnf(c_2460,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | l1_pre_topc(k6_tmap_1(sK1,X0_52)) ),
    inference(subtyping,[status(esa)],[c_563])).

cnf(c_2611,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2460])).

cnf(c_2613,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2611])).

cnf(c_7295,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_52,X1_52),X0_55) = iProver_top
    | v3_pre_topc(X1_52,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_52,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5413,c_36,c_2613])).

cnf(c_7296,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_52,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_52,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_52,X1_52),X0_55) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_7295])).

cnf(c_7305,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_52,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_52,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_52,X1_52),X0_55) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_5246,c_7296])).

cnf(c_38517,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3522,c_7305])).

cnf(c_35,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_39,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2504,plain,
    ( X0_55 != X1_55
    | u1_struct_0(X0_55) = u1_struct_0(X1_55) ),
    theory(equality)).

cnf(c_2521,plain,
    ( sK1 != sK1
    | u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2504])).

cnf(c_2491,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_2535,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2491])).

cnf(c_2493,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2537,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2493])).

cnf(c_2494,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_2538,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_2494])).

cnf(c_17,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_386,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_32])).

cnf(c_387,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_391,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_31,c_30])).

cnf(c_2469,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_52),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_52)))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_391])).

cnf(c_2584,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_52),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_52))) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2469])).

cnf(c_2586,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2584])).

cnf(c_21,plain,
    ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_446,plain,
    ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_447,plain,
    ( v3_pre_topc(X0,k6_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_451,plain,
    ( v3_pre_topc(X0,k6_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_31,c_30])).

cnf(c_2466,plain,
    ( v3_pre_topc(X0_52,k6_tmap_1(sK1,X0_52))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_52))))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_451])).

cnf(c_2593,plain,
    ( v3_pre_topc(X0_52,k6_tmap_1(sK1,X0_52)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_52)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2466])).

cnf(c_2595,plain,
    ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2593])).

cnf(c_2597,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2465])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_32])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k7_tmap_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_508,plain,
    ( v1_funct_1(k7_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_504,c_31,c_30])).

cnf(c_509,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_508])).

cnf(c_2463,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,X0_52)) ),
    inference(subtyping,[status(esa)],[c_509])).

cnf(c_2602,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2463])).

cnf(c_2604,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2602])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_522,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_31,c_30])).

cnf(c_2462,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_52))))) ),
    inference(subtyping,[status(esa)],[c_526])).

cnf(c_2605,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_52))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2462])).

cnf(c_2607,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2605])).

cnf(c_2612,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2460])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_576,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_576,c_31,c_30])).

cnf(c_2459,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,X0_52) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_580])).

cnf(c_2615,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,sK2) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2459])).

cnf(c_2502,plain,
    ( X0_54 != X1_54
    | k1_zfmisc_1(X0_54) = k1_zfmisc_1(X1_54) ),
    theory(equality)).

cnf(c_3711,plain,
    ( X0_54 != u1_struct_0(sK1)
    | k1_zfmisc_1(X0_54) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2502])).

cnf(c_3890,plain,
    ( u1_struct_0(k6_tmap_1(sK1,X0_52)) != u1_struct_0(sK1)
    | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_52))) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3711])).

cnf(c_3891,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3890])).

cnf(c_2497,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_3735,plain,
    ( X0_54 != X1_54
    | X0_54 = u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(k6_tmap_1(sK1,sK2)) != X1_54 ),
    inference(instantiation,[status(thm)],[c_2497])).

cnf(c_4028,plain,
    ( X0_54 = u1_struct_0(k6_tmap_1(sK1,sK2))
    | X0_54 != k2_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(k6_tmap_1(sK1,sK2)) != k2_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3735])).

cnf(c_4030,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) != k2_struct_0(k6_tmap_1(sK1,sK2))
    | k1_xboole_0 = u1_struct_0(k6_tmap_1(sK1,sK2))
    | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_4028])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_372,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_1])).

cnf(c_2470,plain,
    ( ~ l1_pre_topc(X0_55)
    | u1_struct_0(X0_55) = k2_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_372])).

cnf(c_4029,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
    | u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2470])).

cnf(c_2503,plain,
    ( ~ m1_subset_1(X0_52,X0_53)
    | m1_subset_1(X1_52,X1_53)
    | X1_53 != X0_53
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_3561,plain,
    ( m1_subset_1(X0_52,X0_53)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_53 != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_52 != sK2 ),
    inference(instantiation,[status(thm)],[c_2503])).

cnf(c_3710,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(X0_54))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_zfmisc_1(X0_54) != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_52 != sK2 ),
    inference(instantiation,[status(thm)],[c_3561])).

cnf(c_4327,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_52))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_52))) != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_52 != sK2 ),
    inference(instantiation,[status(thm)],[c_3710])).

cnf(c_4328,plain,
    ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_52))) != k1_zfmisc_1(u1_struct_0(sK1))
    | X1_52 != sK2
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_52)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4327])).

cnf(c_4330,plain,
    ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4328])).

cnf(c_4023,plain,
    ( X0_54 = u1_struct_0(k6_tmap_1(sK1,sK2))
    | X0_54 != u1_struct_0(sK1)
    | u1_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3735])).

cnf(c_4573,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4023])).

cnf(c_3886,plain,
    ( k2_struct_0(X0_55) = k2_struct_0(X0_55) ),
    inference(instantiation,[status(thm)],[c_2493])).

cnf(c_5621,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3886])).

cnf(c_5622,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) != k2_struct_0(k6_tmap_1(sK1,sK2))
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(k6_tmap_1(sK1,sK2))
    | k2_struct_0(k6_tmap_1(sK1,sK2)) != k2_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_4028])).

cnf(c_6503,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,sK2))) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3711])).

cnf(c_2500,plain,
    ( X0_54 != X1_54
    | k6_partfun1(X0_54) = k6_partfun1(X1_54) ),
    theory(equality)).

cnf(c_4338,plain,
    ( X0_54 != u1_struct_0(sK1)
    | k6_partfun1(X0_54) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2500])).

cnf(c_6496,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2))) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4338])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2480,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v5_pre_topc(X0_52,X0_55,X1_55)
    | ~ v3_pre_topc(X1_52,X1_55)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_52,X1_52),X0_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | k2_struct_0(X0_55) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_5293,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X1_52)))
    | ~ v5_pre_topc(X0_52,X0_55,k6_tmap_1(sK1,X1_52))
    | ~ v3_pre_topc(X1_52,k6_tmap_1(sK1,X1_52))
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X1_52)),X0_52,X1_52),X0_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X1_52)))))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_52))))
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(k6_tmap_1(sK1,X1_52))
    | k2_struct_0(X0_55) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2480])).

cnf(c_7050,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X0_52)))
    | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,k6_tmap_1(sK1,X0_52))
    | ~ v3_pre_topc(X0_52,k6_tmap_1(sK1,X0_52))
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X0_52)),k7_tmap_1(sK1,sK2),X0_52),X0_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_52))))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X0_52)))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(k6_tmap_1(sK1,X0_52))
    | k2_struct_0(X0_55) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5293])).

cnf(c_7051,plain,
    ( k2_struct_0(X0_55) != k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X0_52))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,k6_tmap_1(sK1,X0_52)) != iProver_top
    | v3_pre_topc(X0_52,k6_tmap_1(sK1,X0_52)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X0_52)),k7_tmap_1(sK1,sK2),X0_52),X0_55) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_52)))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X0_52))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7050])).

cnf(c_7053,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),sK2),sK1) = iProver_top
    | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7051])).

cnf(c_3421,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2460])).

cnf(c_7322,plain,
    ( l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3408,c_3421])).

cnf(c_3411,plain,
    ( u1_struct_0(X0_55) = k2_struct_0(X0_55)
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2470])).

cnf(c_7448,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_7322,c_3411])).

cnf(c_9232,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_7448,c_5246])).

cnf(c_5203,plain,
    ( X0_54 != X1_54
    | X0_54 = u1_struct_0(X0_55)
    | u1_struct_0(X0_55) != X1_54 ),
    inference(instantiation,[status(thm)],[c_2497])).

cnf(c_10112,plain,
    ( X0_54 = u1_struct_0(X0_55)
    | X0_54 != k2_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(X0_55) != k2_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5203])).

cnf(c_10114,plain,
    ( u1_struct_0(sK1) != k2_struct_0(k6_tmap_1(sK1,sK2))
    | k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_10112])).

cnf(c_3917,plain,
    ( m1_subset_1(X0_52,X0_53)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_53 != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_52 != X1_52 ),
    inference(instantiation,[status(thm)],[c_2503])).

cnf(c_12661,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,X2_52))))
    | k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,X2_52))) != k1_zfmisc_1(u1_struct_0(sK1))
    | X1_52 != X0_52 ),
    inference(instantiation,[status(thm)],[c_3917])).

cnf(c_12663,plain,
    ( k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,X0_52))) != k1_zfmisc_1(u1_struct_0(sK1))
    | X1_52 != X2_52
    | m1_subset_1(X2_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,X0_52)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12661])).

cnf(c_12665,plain,
    ( k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_12663])).

cnf(c_5074,plain,
    ( X0_54 != X1_54
    | u1_struct_0(sK1) != X1_54
    | u1_struct_0(sK1) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2497])).

cnf(c_8972,plain,
    ( X0_54 != u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) = X0_54
    | u1_struct_0(sK1) != u1_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5074])).

cnf(c_12687,plain,
    ( u1_struct_0(sK1) != u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) = k2_struct_0(k6_tmap_1(sK1,sK2))
    | k2_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_8972])).

cnf(c_2496,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_4101,plain,
    ( X0_52 != X1_52
    | k7_tmap_1(sK1,X2_52) != X1_52
    | k7_tmap_1(sK1,X2_52) = X0_52 ),
    inference(instantiation,[status(thm)],[c_2496])).

cnf(c_5869,plain,
    ( X0_52 != k6_partfun1(u1_struct_0(sK1))
    | k7_tmap_1(sK1,X1_52) = X0_52
    | k7_tmap_1(sK1,X1_52) != k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4101])).

cnf(c_12762,plain,
    ( k7_tmap_1(sK1,X0_52) != k6_partfun1(u1_struct_0(sK1))
    | k7_tmap_1(sK1,X0_52) = k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2)))
    | k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2))) != k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_5869])).

cnf(c_12766,plain,
    ( k7_tmap_1(sK1,sK2) != k6_partfun1(u1_struct_0(sK1))
    | k7_tmap_1(sK1,sK2) = k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2)))
    | k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2))) != k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_12762])).

cnf(c_4317,plain,
    ( X0_52 != X1_52
    | X1_52 = X0_52 ),
    inference(resolution,[status(thm)],[c_2496,c_2491])).

cnf(c_7213,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X0_54))
    | X0_52 = k8_relset_1(X0_54,X0_54,k6_partfun1(X0_54),X0_52) ),
    inference(resolution,[status(thm)],[c_4317,c_2489])).

cnf(c_2513,plain,
    ( ~ v3_pre_topc(X0_52,X0_55)
    | v3_pre_topc(X1_52,X1_55)
    | X1_55 != X0_55
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_22360,plain,
    ( v3_pre_topc(X0_52,X0_55)
    | ~ v3_pre_topc(k8_relset_1(X0_54,X0_54,k6_partfun1(X0_54),X0_52),X1_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(X0_54))
    | X0_55 != X1_55 ),
    inference(resolution,[status(thm)],[c_7213,c_2513])).

cnf(c_22361,plain,
    ( X0_55 != X1_55
    | v3_pre_topc(X0_52,X0_55) = iProver_top
    | v3_pre_topc(k8_relset_1(X0_54,X0_54,k6_partfun1(X0_54),X0_52),X1_55) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22360])).

cnf(c_22363,plain,
    ( sK1 != sK1
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2),sK1) != iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_22361])).

cnf(c_2476,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3405,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2476])).

cnf(c_3422,plain,
    ( k7_tmap_1(sK1,X0_52) = k6_partfun1(u1_struct_0(sK1))
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2459])).

cnf(c_7776,plain,
    ( k7_tmap_1(sK1,sK2) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_3408,c_3422])).

cnf(c_25,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2477,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3404,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2477])).

cnf(c_3648,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3404,c_36,c_2607])).

cnf(c_7301,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X0_52,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k7_tmap_1(sK1,sK2),X0_52),sK1) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3648,c_7296])).

cnf(c_36429,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X0_52,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k7_tmap_1(sK1,sK2),X0_52),sK1) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7301,c_35,c_36,c_2586,c_2604])).

cnf(c_36438,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X0_52,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),X0_52),sK1) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7776,c_36429])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2485,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_52,X0_55,X1_55)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_52,sK0(X0_55,X1_55,X0_52)),X0_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | k2_struct_0(X1_55) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3396,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_52,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_52,X1_55,X0_55) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X0_55),X0_52,sK0(X1_55,X0_55,X0_52)),X1_55) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2485])).

cnf(c_36674,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_36438,c_3396])).

cnf(c_2582,plain,
    ( ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2470])).

cnf(c_24,negated_conjecture,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2478,negated_conjecture,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_2585,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2469])).

cnf(c_2603,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2463])).

cnf(c_2606,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2462])).

cnf(c_2674,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2478,c_29,c_24,c_2585,c_2603,c_2606])).

cnf(c_2676,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2674])).

cnf(c_3888,plain,
    ( k2_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3886])).

cnf(c_4940,plain,
    ( X0_54 != X1_54
    | X0_54 = k2_struct_0(k6_tmap_1(sK1,sK2))
    | k2_struct_0(k6_tmap_1(sK1,sK2)) != X1_54 ),
    inference(instantiation,[status(thm)],[c_2497])).

cnf(c_4941,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK1,sK2))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4940])).

cnf(c_3889,plain,
    ( X0_54 != X1_54
    | k2_struct_0(X0_55) != X1_54
    | k2_struct_0(X0_55) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2497])).

cnf(c_5980,plain,
    ( X0_54 != k2_struct_0(X0_55)
    | k2_struct_0(X0_55) = X0_54
    | k2_struct_0(X0_55) != k2_struct_0(X0_55) ),
    inference(instantiation,[status(thm)],[c_3889])).

cnf(c_7076,plain,
    ( u1_struct_0(X0_55) != k2_struct_0(X0_55)
    | k2_struct_0(X0_55) = u1_struct_0(X0_55)
    | k2_struct_0(X0_55) != k2_struct_0(X0_55) ),
    inference(instantiation,[status(thm)],[c_5980])).

cnf(c_7077,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) = u1_struct_0(sK1)
    | k2_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7076])).

cnf(c_7083,plain,
    ( k2_struct_0(X0_55) != k2_struct_0(X0_55)
    | k2_struct_0(X0_55) = k2_struct_0(k6_tmap_1(sK1,sK2))
    | k2_struct_0(k6_tmap_1(sK1,sK2)) != k2_struct_0(X0_55) ),
    inference(instantiation,[status(thm)],[c_5980])).

cnf(c_7085,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) != k2_struct_0(sK1)
    | k2_struct_0(sK1) = k2_struct_0(k6_tmap_1(sK1,sK2))
    | k2_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7083])).

cnf(c_3666,plain,
    ( k2_struct_0(X0_55) != X0_54
    | k2_struct_0(X0_55) = k1_xboole_0
    | k1_xboole_0 != X0_54 ),
    inference(instantiation,[status(thm)],[c_2497])).

cnf(c_9770,plain,
    ( k2_struct_0(X0_55) != k2_struct_0(k6_tmap_1(sK1,sK2))
    | k2_struct_0(X0_55) = k1_xboole_0
    | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3666])).

cnf(c_9772,plain,
    ( k2_struct_0(sK1) != k2_struct_0(k6_tmap_1(sK1,sK2))
    | k2_struct_0(sK1) = k1_xboole_0
    | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_9770])).

cnf(c_6532,plain,
    ( X0_54 != X1_54
    | k2_struct_0(k6_tmap_1(sK1,sK2)) != X1_54
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = X0_54 ),
    inference(instantiation,[status(thm)],[c_3889])).

cnf(c_8998,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) != X0_54
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1)
    | k2_struct_0(sK1) != X0_54 ),
    inference(instantiation,[status(thm)],[c_6532])).

cnf(c_17915,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1)
    | k2_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_8998])).

cnf(c_36669,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3522,c_36438])).

cnf(c_36680,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36674,c_30,c_29,c_36,c_2535,c_2537,c_2582,c_2595,c_2597,c_2676,c_3888,c_3891,c_4330,c_4941,c_7077,c_7085,c_9232,c_9772,c_17915,c_36669])).

cnf(c_36691,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3405,c_36680])).

cnf(c_2501,plain,
    ( X0_54 != X1_54
    | X2_54 != X3_54
    | X0_52 != X1_52
    | X2_52 != X3_52
    | k8_relset_1(X0_54,X2_54,X0_52,X2_52) = k8_relset_1(X1_54,X3_54,X1_52,X3_52) ),
    theory(equality)).

cnf(c_16074,plain,
    ( ~ v3_pre_topc(k8_relset_1(X0_54,X1_54,X0_52,X1_52),X0_55)
    | v3_pre_topc(k8_relset_1(X2_54,X3_54,X2_52,X3_52),X1_55)
    | X1_55 != X0_55
    | X2_54 != X0_54
    | X3_54 != X1_54
    | X2_52 != X0_52
    | X3_52 != X1_52 ),
    inference(resolution,[status(thm)],[c_2513,c_2501])).

cnf(c_19552,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v5_pre_topc(X0_52,X0_55,X1_55)
    | ~ v3_pre_topc(X1_52,X1_55)
    | v3_pre_topc(k8_relset_1(X0_54,X1_54,X2_52,X3_52),X2_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | X2_55 != X0_55
    | X0_54 != u1_struct_0(X0_55)
    | X1_54 != u1_struct_0(X1_55)
    | k2_struct_0(X1_55) = k1_xboole_0
    | X2_52 != X0_52
    | X3_52 != X1_52 ),
    inference(resolution,[status(thm)],[c_16074,c_2479])).

cnf(c_2679,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2477,c_29,c_2606])).

cnf(c_39950,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(X0_52,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(k8_relset_1(X0_54,X1_54,X1_52,X2_52),X0_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | X0_55 != sK1
    | X1_54 != u1_struct_0(k6_tmap_1(sK1,sK2))
    | X0_54 != u1_struct_0(sK1)
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | X2_52 != X0_52
    | X1_52 != k7_tmap_1(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_19552,c_2679])).

cnf(c_2594,plain,
    ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2466])).

cnf(c_4329,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4327])).

cnf(c_36676,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))))
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_36669])).

cnf(c_39988,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_39950,c_37013])).

cnf(c_40004,plain,
    ( v3_pre_topc(sK2,sK1)
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_39988,c_2476])).

cnf(c_4407,plain,
    ( X0_54 != X1_54
    | X1_54 = X0_54 ),
    inference(resolution,[status(thm)],[c_2497,c_2493])).

cnf(c_40073,plain,
    ( v3_pre_topc(sK2,sK1)
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_40004,c_4407])).

cnf(c_40074,plain,
    ( k1_xboole_0 = k2_struct_0(k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40073])).

cnf(c_4318,plain,
    ( X0_54 != X1_54
    | X0_52 != k6_partfun1(X1_54)
    | k6_partfun1(X0_54) = X0_52 ),
    inference(resolution,[status(thm)],[c_2496,c_2500])).

cnf(c_8426,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | k6_partfun1(X0_54) = k6_partfun1(X2_54) ),
    inference(resolution,[status(thm)],[c_4318,c_2500])).

cnf(c_40076,plain,
    ( v3_pre_topc(sK2,sK1)
    | X0_54 != k1_xboole_0
    | k6_partfun1(X0_54) = k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_40004,c_8426])).

cnf(c_40081,plain,
    ( X0_54 != k1_xboole_0
    | k6_partfun1(X0_54) = k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2)))
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40076])).

cnf(c_40083,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k6_partfun1(k1_xboole_0) = k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2)))
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_40081])).

cnf(c_4216,plain,
    ( ~ m1_subset_1(X0_52,X0_53)
    | m1_subset_1(X0_52,X1_53)
    | X1_53 != X0_53 ),
    inference(resolution,[status(thm)],[c_2503,c_2491])).

cnf(c_7354,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X0_54))
    | m1_subset_1(X0_52,k1_zfmisc_1(X1_54))
    | X1_54 != X0_54 ),
    inference(resolution,[status(thm)],[c_4216,c_2502])).

cnf(c_40147,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,sK2))))
    | m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_40073,c_7354])).

cnf(c_40156,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40147])).

cnf(c_40158,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_40156])).

cnf(c_3684,plain,
    ( X0_52 != X1_52
    | X0_52 = k7_tmap_1(sK1,sK2)
    | k7_tmap_1(sK1,sK2) != X1_52 ),
    inference(instantiation,[status(thm)],[c_2496])).

cnf(c_38969,plain,
    ( X0_52 = k7_tmap_1(sK1,sK2)
    | X0_52 != k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2)))
    | k7_tmap_1(sK1,sK2) != k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_3684])).

cnf(c_56891,plain,
    ( k7_tmap_1(sK1,sK2) != k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2)))
    | k6_partfun1(X0_54) = k7_tmap_1(sK1,sK2)
    | k6_partfun1(X0_54) != k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_38969])).

cnf(c_56893,plain,
    ( k7_tmap_1(sK1,sK2) != k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2)))
    | k6_partfun1(k1_xboole_0) = k7_tmap_1(sK1,sK2)
    | k6_partfun1(k1_xboole_0) != k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_56891])).

cnf(c_70936,plain,
    ( X0_54 != u1_struct_0(k6_tmap_1(sK1,sK2))
    | X1_54 != u1_struct_0(sK1)
    | X0_52 != X1_52
    | X2_52 != k7_tmap_1(sK1,sK2)
    | k8_relset_1(X1_54,X0_54,X2_52,X0_52) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52) ),
    inference(instantiation,[status(thm)],[c_2501])).

cnf(c_72135,plain,
    ( X0_54 != u1_struct_0(k6_tmap_1(sK1,sK2))
    | X1_54 != u1_struct_0(sK1)
    | X0_52 != X1_52
    | k8_relset_1(X1_54,X0_54,k6_partfun1(X2_54),X0_52) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52)
    | k6_partfun1(X2_54) != k7_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_70936])).

cnf(c_72136,plain,
    ( k1_xboole_0 != u1_struct_0(k6_tmap_1(sK1,sK2))
    | k1_xboole_0 != u1_struct_0(sK1)
    | k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),sK2)
    | k6_partfun1(k1_xboole_0) != k7_tmap_1(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_72135])).

cnf(c_70595,plain,
    ( v3_pre_topc(X0_52,X0_55)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52),sK1)
    | X0_55 != sK1
    | X0_52 != k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52) ),
    inference(instantiation,[status(thm)],[c_2513])).

cnf(c_70935,plain,
    ( v3_pre_topc(k8_relset_1(X0_54,X1_54,X0_52,X1_52),X0_55)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X2_52),sK1)
    | X0_55 != sK1
    | k8_relset_1(X0_54,X1_54,X0_52,X1_52) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X2_52) ),
    inference(instantiation,[status(thm)],[c_70595])).

cnf(c_76433,plain,
    ( v3_pre_topc(k8_relset_1(X0_54,X1_54,k6_partfun1(X2_54),X0_52),X0_55)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52),sK1)
    | X0_55 != sK1
    | k8_relset_1(X0_54,X1_54,k6_partfun1(X2_54),X0_52) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52) ),
    inference(instantiation,[status(thm)],[c_70935])).

cnf(c_76434,plain,
    ( X0_55 != sK1
    | k8_relset_1(X0_54,X1_54,k6_partfun1(X2_54),X0_52) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52)
    | v3_pre_topc(k8_relset_1(X0_54,X1_54,k6_partfun1(X2_54),X0_52),X0_55) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76433])).

cnf(c_76436,plain,
    ( sK1 != sK1
    | k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),sK2)
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),sK2),sK1) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_76434])).

cnf(c_76751,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38517,c_35,c_29,c_36,c_39,c_2521,c_2535,c_2537,c_2538,c_2586,c_2595,c_2597,c_2604,c_2607,c_2612,c_2613,c_2615,c_3891,c_4030,c_4029,c_4330,c_4573,c_5621,c_5622,c_6503,c_6496,c_7053,c_9232,c_10114,c_12665,c_12687,c_12766,c_22363,c_36691,c_40074,c_40083,c_40158,c_56893,c_72136,c_76436])).

cnf(c_23,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_404,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_405,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_409,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_31,c_30])).

cnf(c_2468,plain,
    ( ~ v3_pre_topc(X0_52,sK1)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0_52) ),
    inference(subtyping,[status(esa)],[c_409])).

cnf(c_3413,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0_52)
    | v3_pre_topc(X0_52,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2468])).

cnf(c_4389,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3408,c_3413])).

cnf(c_76766,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_76751,c_4389])).

cnf(c_2472,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_3409,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2472])).

cnf(c_4060,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_3409,c_3411])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2487,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))))
    | ~ v5_pre_topc(X0_52,X0_55,X1_55)
    | v5_pre_topc(X0_52,X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3394,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))) != iProver_top
    | v5_pre_topc(X0_52,X0_55,X1_55) != iProver_top
    | v5_pre_topc(X0_52,X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2487])).

cnf(c_76773,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_52,X0_55,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(X0_52,X0_55,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_76766,c_3394])).

cnf(c_34,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_76964,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_52,X0_55,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(X0_52,X0_55,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_76773,c_34,c_35])).

cnf(c_76965,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_52,X0_55,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(X0_52,X0_55,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_76964])).

cnf(c_76968,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_52,k2_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v5_pre_topc(X0_52,sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(X0_52,sK1,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4060,c_76965])).

cnf(c_77676,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_52,k2_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v5_pre_topc(X0_52,sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(X0_52,sK1,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_76968,c_34,c_35])).

cnf(c_77677,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_52,k2_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v5_pre_topc(X0_52,sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(X0_52,sK1,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_77676])).

cnf(c_77682,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k7_tmap_1(sK1,sK2),k2_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3648,c_77677])).

cnf(c_2514,plain,
    ( X0_55 != X1_55
    | X0_52 != X1_52
    | k7_tmap_1(X0_55,X0_52) = k7_tmap_1(X1_55,X1_52) ),
    theory(equality)).

cnf(c_2531,plain,
    ( sK1 != sK1
    | k7_tmap_1(sK1,sK2) = k7_tmap_1(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2514])).

cnf(c_3925,plain,
    ( X0_52 = k7_tmap_1(sK1,sK2)
    | X0_52 != k6_partfun1(u1_struct_0(sK1))
    | k7_tmap_1(sK1,sK2) != k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3684])).

cnf(c_4333,plain,
    ( k7_tmap_1(sK1,sK2) != k6_partfun1(u1_struct_0(sK1))
    | k6_partfun1(u1_struct_0(sK1)) = k7_tmap_1(sK1,sK2)
    | k6_partfun1(u1_struct_0(sK1)) != k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3925])).

cnf(c_4334,plain,
    ( k6_partfun1(u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2491])).

cnf(c_2511,plain,
    ( ~ v1_funct_1(X0_52)
    | v1_funct_1(X1_52)
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_3539,plain,
    ( v1_funct_1(X0_52)
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | X0_52 != k7_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2511])).

cnf(c_4905,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
    | k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3539])).

cnf(c_4906,plain,
    ( k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,sK2)
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4905])).

cnf(c_5403,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5246,c_3648])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2475,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | v3_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3406,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2475])).

cnf(c_3625,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3406,c_36,c_2586])).

cnf(c_5404,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5246,c_3625])).

cnf(c_2506,plain,
    ( ~ v5_pre_topc(X0_52,X0_55,X1_55)
    | v5_pre_topc(X1_52,X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_6117,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,X0_52),X0_55,X1_55)
    | ~ v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X2_55,X3_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_55 != X2_55
    | X1_55 != X3_55 ),
    inference(resolution,[status(thm)],[c_2506,c_2459])).

cnf(c_6118,plain,
    ( X0_55 != X1_55
    | X2_55 != X3_55
    | v5_pre_topc(k7_tmap_1(sK1,X0_52),X0_55,X2_55) = iProver_top
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X1_55,X3_55) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6117])).

cnf(c_6120,plain,
    ( sK1 != sK1
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6118])).

cnf(c_2510,plain,
    ( ~ v1_funct_2(X0_52,X0_54,X1_54)
    | v1_funct_2(X1_52,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_3604,plain,
    ( v1_funct_2(X0_52,X0_54,X1_54)
    | ~ v1_funct_2(k7_tmap_1(sK1,X1_52),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1_52)))
    | X1_54 != u1_struct_0(k6_tmap_1(sK1,X1_52))
    | X0_54 != u1_struct_0(sK1)
    | X0_52 != k7_tmap_1(sK1,X1_52) ),
    inference(instantiation,[status(thm)],[c_2510])).

cnf(c_3806,plain,
    ( v1_funct_2(X0_52,X0_54,u1_struct_0(X0_55))
    | ~ v1_funct_2(k7_tmap_1(sK1,X1_52),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1_52)))
    | X0_54 != u1_struct_0(sK1)
    | u1_struct_0(X0_55) != u1_struct_0(k6_tmap_1(sK1,X1_52))
    | X0_52 != k7_tmap_1(sK1,X1_52) ),
    inference(instantiation,[status(thm)],[c_3604])).

cnf(c_4574,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK1),u1_struct_0(X0_55))
    | ~ v1_funct_2(k7_tmap_1(sK1,X1_52),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1_52)))
    | u1_struct_0(X0_55) != u1_struct_0(k6_tmap_1(sK1,X1_52))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | X0_52 != k7_tmap_1(sK1,X1_52) ),
    inference(instantiation,[status(thm)],[c_3806])).

cnf(c_6200,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(X0_55))
    | u1_struct_0(X0_55) != u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_4574])).

cnf(c_6201,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,sK2)
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6200])).

cnf(c_6203,plain,
    ( u1_struct_0(sK1) != u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,sK2)
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6201])).

cnf(c_3914,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),X0_52) = X0_52 ),
    inference(instantiation,[status(thm)],[c_2489])).

cnf(c_7045,plain,
    ( ~ m1_subset_1(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))) = sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_3914])).

cnf(c_7048,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))) = sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7045])).

cnf(c_6185,plain,
    ( v1_funct_2(k7_tmap_1(X0_55,X0_52),u1_struct_0(sK1),u1_struct_0(X1_55))
    | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | u1_struct_0(X1_55) != u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k7_tmap_1(X0_55,X0_52) != k7_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_4574])).

cnf(c_8665,plain,
    ( v1_funct_2(k7_tmap_1(X0_55,X0_52),u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))))
    | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) != u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k7_tmap_1(X0_55,X0_52) != k7_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_6185])).

cnf(c_8667,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55))) != u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k7_tmap_1(X1_55,X0_52) != k7_tmap_1(sK1,sK2)
    | v1_funct_2(k7_tmap_1(X1_55,X0_52),u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)))) = iProver_top
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8665])).

cnf(c_8669,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k7_tmap_1(sK1,sK2) != k7_tmap_1(sK1,sK2)
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8667])).

cnf(c_4487,plain,
    ( ~ v3_pre_topc(X0_52,X0_55)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X2_55),X1_52,sK0(X1_55,X2_55,X1_52)),X1_55)
    | X1_55 != X0_55
    | k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X2_55),X1_52,sK0(X1_55,X2_55,X1_52)) != X0_52 ),
    inference(instantiation,[status(thm)],[c_2513])).

cnf(c_10820,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X0_55),k6_partfun1(u1_struct_0(X0_55)),sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55)))),X0_55)
    | ~ v3_pre_topc(sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55))),X1_55)
    | X0_55 != X1_55
    | k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X0_55),k6_partfun1(u1_struct_0(X0_55)),sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55)))) != sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55))) ),
    inference(instantiation,[status(thm)],[c_4487])).

cnf(c_10823,plain,
    ( X0_55 != X1_55
    | k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X0_55),k6_partfun1(u1_struct_0(X0_55)),sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55)))) != sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55)))
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X0_55),k6_partfun1(u1_struct_0(X0_55)),sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55)))),X0_55) = iProver_top
    | v3_pre_topc(sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55))),X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10820])).

cnf(c_10825,plain,
    ( sK1 != sK1
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))) != sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))),sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10823])).

cnf(c_12786,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7776,c_5403])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v3_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2483,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_52,X0_55,X1_55)
    | v3_pre_topc(sK0(X0_55,X1_55,X0_52),X1_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | k2_struct_0(X1_55) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3398,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_52,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_52,X1_55,X0_55) = iProver_top
    | v3_pre_topc(sK0(X1_55,X0_55,X0_52),X0_55) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2483])).

cnf(c_12791,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,k7_tmap_1(sK1,sK2)),sK1) = iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5403,c_3398])).

cnf(c_3615,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,X1_55)
    | v3_pre_topc(sK0(X0_55,X1_55,k7_tmap_1(sK1,sK2)),X1_55)
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | k2_struct_0(X1_55) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2483])).

cnf(c_3616,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),X1_55,X0_55) = iProver_top
    | v3_pre_topc(sK0(X1_55,X0_55,k7_tmap_1(sK1,sK2)),X0_55) = iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3615])).

cnf(c_3618,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,k7_tmap_1(sK1,sK2)),sK1) = iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3616])).

cnf(c_12799,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,k7_tmap_1(sK1,sK2)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12791,c_35,c_36,c_2604,c_3618,c_5403,c_5404])).

cnf(c_12803,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7776,c_12799])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v3_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2484,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_52,X0_55,X1_55)
    | v3_pre_topc(sK0(X0_55,X1_55,X0_52),X1_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | k2_struct_0(X0_55) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_7209,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | k6_partfun1(u1_struct_0(sK1)) = k7_tmap_1(sK1,X0_52) ),
    inference(resolution,[status(thm)],[c_4317,c_2459])).

cnf(c_7368,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k7_tmap_1(sK1,X0_52),X0_53)
    | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),X1_53)
    | X1_53 != X0_53 ),
    inference(resolution,[status(thm)],[c_7209,c_2503])).

cnf(c_10685,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),X0_53)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_53 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))) ),
    inference(resolution,[status(thm)],[c_7368,c_2679])).

cnf(c_10700,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),X0_53)
    | X0_53 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10685,c_29])).

cnf(c_11146,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(X0_54))
    | X0_54 != k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_10700,c_2502])).

cnf(c_2509,plain,
    ( X0_54 != X1_54
    | X2_54 != X3_54
    | k2_zfmisc_1(X0_54,X2_54) = k2_zfmisc_1(X1_54,X3_54) ),
    theory(equality)).

cnf(c_11161,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | X1_54 != u1_struct_0(k6_tmap_1(sK1,sK2))
    | X0_54 != u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_11146,c_2509])).

cnf(c_15306,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X0_55,X1_55)
    | v3_pre_topc(sK0(X0_55,X1_55,k6_partfun1(u1_struct_0(sK1))),X1_55)
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | u1_struct_0(X1_55) != u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(X0_55) != u1_struct_0(sK1)
    | k2_struct_0(X0_55) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2484,c_11161])).

cnf(c_15307,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | k2_struct_0(X1_55) != k1_xboole_0
    | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X1_55,X0_55) = iProver_top
    | v3_pre_topc(sK0(X1_55,X0_55,k6_partfun1(u1_struct_0(sK1))),X0_55) = iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15306])).

cnf(c_15309,plain,
    ( u1_struct_0(sK1) != u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),sK1) = iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15307])).

cnf(c_19078,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12803,c_35,c_29,c_36,c_2521,c_2538,c_2586,c_2597,c_2604,c_2615,c_4333,c_4334,c_4573,c_4906,c_6120,c_6203,c_15309])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2481,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_52,X0_55,X1_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | m1_subset_1(sK0(X0_55,X1_55,X0_52),k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | k2_struct_0(X1_55) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3400,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_52,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_52,X1_55,X0_55) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(sK0(X1_55,X0_55,X0_52),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2481])).

cnf(c_12790,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
    | m1_subset_1(sK0(sK1,sK1,k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5403,c_3400])).

cnf(c_3607,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,X1_55)
    | m1_subset_1(sK0(X0_55,X1_55,k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | k2_struct_0(X1_55) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2481])).

cnf(c_3608,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),X1_55,X0_55) = iProver_top
    | m1_subset_1(sK0(X1_55,X0_55,k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3607])).

cnf(c_3610,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
    | m1_subset_1(sK0(sK1,sK1,k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3608])).

cnf(c_13005,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
    | m1_subset_1(sK0(sK1,sK1,k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12790,c_35,c_36,c_2604,c_3610,c_5403,c_5404])).

cnf(c_13009,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
    | m1_subset_1(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7776,c_13005])).

cnf(c_21839,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))) = sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_13009,c_3392])).

cnf(c_4408,plain,
    ( X0_55 != X1_55
    | X0_54 != u1_struct_0(X1_55)
    | u1_struct_0(X0_55) = X0_54 ),
    inference(resolution,[status(thm)],[c_2497,c_2504])).

cnf(c_8442,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | u1_struct_0(X0_55) = u1_struct_0(X2_55) ),
    inference(resolution,[status(thm)],[c_4408,c_2504])).

cnf(c_25516,plain,
    ( ~ v3_pre_topc(X0_52,sK1)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_55 != k6_tmap_1(sK1,X0_52)
    | u1_struct_0(X0_55) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[status(thm)],[c_8442,c_2468])).

cnf(c_25808,plain,
    ( ~ v3_pre_topc(X0_52,sK1)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0_52)) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[status(thm)],[c_25516,c_2494])).

cnf(c_27784,plain,
    ( ~ v3_pre_topc(X0_52,sK1)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(k6_tmap_1(sK1,X0_52)) ),
    inference(resolution,[status(thm)],[c_25808,c_4407])).

cnf(c_27785,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(k6_tmap_1(sK1,X0_52))
    | v3_pre_topc(X0_52,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27784])).

cnf(c_27787,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_27785])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2482,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_52,X0_55,X1_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | m1_subset_1(sK0(X0_55,X1_55,X0_52),k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | k2_struct_0(X0_55) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_34401,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X0_55,X1_55)
    | m1_subset_1(sK0(X0_55,X1_55,k6_partfun1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | k2_struct_0(X0_55) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2482])).

cnf(c_34402,plain,
    ( k2_struct_0(X0_55) != k1_xboole_0
    | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X0_55,X1_55) = iProver_top
    | m1_subset_1(sK0(X0_55,X1_55,k6_partfun1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(X1_55))) = iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34401])).

cnf(c_34404,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,sK1) = iProver_top
    | m1_subset_1(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34402])).

cnf(c_38106,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X0_55,X1_55)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),k6_partfun1(u1_struct_0(sK1)),sK0(X0_55,X1_55,k6_partfun1(u1_struct_0(sK1)))),X0_55)
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | k2_struct_0(X1_55) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2485])).

cnf(c_38111,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X1_55,X0_55) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X0_55),k6_partfun1(u1_struct_0(sK1)),sK0(X1_55,X0_55,k6_partfun1(u1_struct_0(sK1)))),X1_55) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38106])).

cnf(c_38113,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))),sK1) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38111])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2486,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_52,X0_55,X1_55)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_52,sK0(X0_55,X1_55,X0_52)),X0_55)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(X0_52)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | k2_struct_0(X0_55) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_38105,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X0_55,X1_55)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),k6_partfun1(u1_struct_0(sK1)),sK0(X0_55,X1_55,k6_partfun1(u1_struct_0(sK1)))),X0_55)
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | k2_struct_0(X0_55) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2486])).

cnf(c_38115,plain,
    ( k2_struct_0(X0_55) != k1_xboole_0
    | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X0_55,X1_55) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),k6_partfun1(u1_struct_0(sK1)),sK0(X0_55,X1_55,k6_partfun1(u1_struct_0(sK1)))),X0_55) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38105])).

cnf(c_38117,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))),sK1) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38115])).

cnf(c_22400,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54)))
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    inference(resolution,[status(thm)],[c_7354,c_2509])).

cnf(c_59293,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | X1_54 != u1_struct_0(k6_tmap_1(sK1,sK2))
    | X0_54 != u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_22400,c_2679])).

cnf(c_59551,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))))
    | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,X1_55)
    | v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | u1_struct_0(X0_55) != u1_struct_0(sK1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) != u1_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_59293,c_2487])).

cnf(c_59556,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) != u1_struct_0(k6_tmap_1(sK1,sK2))
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,X1_55) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) = iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59551])).

cnf(c_59558,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != u1_struct_0(k6_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_59556])).

cnf(c_78090,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_77682,c_34,c_35,c_29,c_36,c_39,c_2521,c_2531,c_2535,c_2537,c_2538,c_2586,c_2595,c_2597,c_2604,c_2607,c_2612,c_2613,c_2615,c_3891,c_4030,c_4029,c_4330,c_4333,c_4334,c_4573,c_4906,c_5403,c_5404,c_5621,c_5622,c_6120,c_6203,c_6503,c_6496,c_7048,c_7053,c_8669,c_9232,c_10114,c_10825,c_12665,c_12687,c_12766,c_12786,c_19078,c_21839,c_22363,c_27787,c_34404,c_36691,c_38113,c_38117,c_40074,c_40083,c_40158,c_56893,c_59558,c_72136,c_76436])).

cnf(c_78096,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_76766,c_78090])).

cnf(c_41,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_78096,c_76751,c_38117,c_38113,c_34404,c_21839,c_19078,c_12786,c_10825,c_7048,c_6203,c_6120,c_4906,c_4573,c_4334,c_4333,c_2615,c_2607,c_2604,c_2597,c_2586,c_2538,c_2521,c_41,c_36,c_29,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.71/4.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.71/4.00  
% 27.71/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.71/4.00  
% 27.71/4.00  ------  iProver source info
% 27.71/4.00  
% 27.71/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.71/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.71/4.00  git: non_committed_changes: false
% 27.71/4.00  git: last_make_outside_of_git: false
% 27.71/4.00  
% 27.71/4.00  ------ 
% 27.71/4.00  ------ Parsing...
% 27.71/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.71/4.00  
% 27.71/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.71/4.00  
% 27.71/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.71/4.00  
% 27.71/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.71/4.00  ------ Proving...
% 27.71/4.00  ------ Problem Properties 
% 27.71/4.00  
% 27.71/4.00  
% 27.71/4.00  clauses                                 31
% 27.71/4.00  conjectures                             8
% 27.71/4.00  EPR                                     2
% 27.71/4.00  Horn                                    21
% 27.71/4.00  unary                                   3
% 27.71/4.00  binary                                  14
% 27.71/4.00  lits                                    135
% 27.71/4.00  lits eq                                 15
% 27.71/4.00  fd_pure                                 0
% 27.71/4.00  fd_pseudo                               0
% 27.71/4.00  fd_cond                                 0
% 27.71/4.00  fd_pseudo_cond                          0
% 27.71/4.00  AC symbols                              0
% 27.71/4.00  
% 27.71/4.00  ------ Input Options Time Limit: Unbounded
% 27.71/4.00  
% 27.71/4.00  
% 27.71/4.00  ------ 
% 27.71/4.00  Current options:
% 27.71/4.00  ------ 
% 27.71/4.00  
% 27.71/4.00  
% 27.71/4.00  
% 27.71/4.00  
% 27.71/4.00  ------ Proving...
% 27.71/4.00  
% 27.71/4.00  
% 27.71/4.00  % SZS status Theorem for theBenchmark.p
% 27.71/4.00  
% 27.71/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.71/4.00  
% 27.71/4.00  fof(f12,conjecture,(
% 27.71/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 27.71/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.71/4.00  
% 27.71/4.00  fof(f13,negated_conjecture,(
% 27.71/4.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 27.71/4.00    inference(negated_conjecture,[],[f12])).
% 27.71/4.00  
% 27.71/4.00  fof(f34,plain,(
% 27.71/4.00    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 27.71/4.00    inference(ennf_transformation,[],[f13])).
% 27.71/4.00  
% 27.71/4.00  fof(f35,plain,(
% 27.71/4.00    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 27.71/4.00    inference(flattening,[],[f34])).
% 27.71/4.00  
% 27.71/4.00  fof(f42,plain,(
% 27.71/4.00    ? [X0] : (? [X1] : ((((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 27.71/4.00    inference(nnf_transformation,[],[f35])).
% 27.71/4.00  
% 27.71/4.00  fof(f43,plain,(
% 27.71/4.00    ? [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 27.71/4.00    inference(flattening,[],[f42])).
% 27.71/4.00  
% 27.71/4.00  fof(f45,plain,(
% 27.71/4.00    ( ! [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~m1_subset_1(k7_tmap_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))))) | ~v5_pre_topc(k7_tmap_1(X0,sK2),X0,k6_tmap_1(X0,sK2)) | ~v1_funct_2(k7_tmap_1(X0,sK2),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))) | ~v1_funct_1(k7_tmap_1(X0,sK2)) | ~v3_pre_topc(sK2,X0)) & ((m1_subset_1(k7_tmap_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))))) & v5_pre_topc(k7_tmap_1(X0,sK2),X0,k6_tmap_1(X0,sK2)) & v1_funct_2(k7_tmap_1(X0,sK2),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))) & v1_funct_1(k7_tmap_1(X0,sK2))) | v3_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.71/4.00    introduced(choice_axiom,[])).
% 27.71/4.00  
% 27.71/4.00  fof(f44,plain,(
% 27.71/4.00    ? [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k7_tmap_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))))) | ~v5_pre_topc(k7_tmap_1(sK1,X1),sK1,k6_tmap_1(sK1,X1)) | ~v1_funct_2(k7_tmap_1(sK1,X1),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))) | ~v1_funct_1(k7_tmap_1(sK1,X1)) | ~v3_pre_topc(X1,sK1)) & ((m1_subset_1(k7_tmap_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))))) & v5_pre_topc(k7_tmap_1(sK1,X1),sK1,k6_tmap_1(sK1,X1)) & v1_funct_2(k7_tmap_1(sK1,X1),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))) & v1_funct_1(k7_tmap_1(sK1,X1))) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 27.71/4.00    introduced(choice_axiom,[])).
% 27.71/4.00  
% 27.71/4.00  fof(f46,plain,(
% 27.71/4.00    ((~m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) | ~v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) | ~v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) | ~v1_funct_1(k7_tmap_1(sK1,sK2)) | ~v3_pre_topc(sK2,sK1)) & ((m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) & v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) & v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) & v1_funct_1(k7_tmap_1(sK1,sK2))) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 27.71/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f45,f44])).
% 27.71/4.00  
% 27.71/4.00  fof(f74,plain,(
% 27.71/4.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 27.71/4.00    inference(cnf_transformation,[],[f46])).
% 27.71/4.00  
% 27.71/4.00  fof(f1,axiom,(
% 27.71/4.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 27.71/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.71/4.00  
% 27.71/4.00  fof(f15,plain,(
% 27.71/4.00    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.71/4.00    inference(ennf_transformation,[],[f1])).
% 27.71/4.00  
% 27.71/4.00  fof(f47,plain,(
% 27.71/4.00    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.71/4.00    inference(cnf_transformation,[],[f15])).
% 27.71/4.00  
% 27.71/4.00  fof(f9,axiom,(
% 27.71/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 27.71/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.71/4.00  
% 27.71/4.00  fof(f28,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.71/4.00    inference(ennf_transformation,[],[f9])).
% 27.71/4.00  
% 27.71/4.00  fof(f29,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.71/4.00    inference(flattening,[],[f28])).
% 27.71/4.00  
% 27.71/4.00  fof(f66,plain,(
% 27.71/4.00    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f29])).
% 27.71/4.00  
% 27.71/4.00  fof(f71,plain,(
% 27.71/4.00    ~v2_struct_0(sK1)),
% 27.71/4.00    inference(cnf_transformation,[],[f46])).
% 27.71/4.00  
% 27.71/4.00  fof(f72,plain,(
% 27.71/4.00    v2_pre_topc(sK1)),
% 27.71/4.00    inference(cnf_transformation,[],[f46])).
% 27.71/4.00  
% 27.71/4.00  fof(f73,plain,(
% 27.71/4.00    l1_pre_topc(sK1)),
% 27.71/4.00    inference(cnf_transformation,[],[f46])).
% 27.71/4.00  
% 27.71/4.00  fof(f5,axiom,(
% 27.71/4.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_struct_0(X1) = k1_xboole_0 => k2_struct_0(X0) = k1_xboole_0) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 27.71/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.71/4.00  
% 27.71/4.00  fof(f20,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.71/4.00    inference(ennf_transformation,[],[f5])).
% 27.71/4.00  
% 27.71/4.00  fof(f21,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.71/4.00    inference(flattening,[],[f20])).
% 27.71/4.00  
% 27.71/4.00  fof(f37,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.71/4.00    inference(nnf_transformation,[],[f21])).
% 27.71/4.00  
% 27.71/4.00  fof(f38,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.71/4.00    inference(rectify,[],[f37])).
% 27.71/4.00  
% 27.71/4.00  fof(f39,plain,(
% 27.71/4.00    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v3_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 27.71/4.00    introduced(choice_axiom,[])).
% 27.71/4.00  
% 27.71/4.00  fof(f40,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v3_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.71/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 27.71/4.00  
% 27.71/4.00  fof(f52,plain,(
% 27.71/4.00    ( ! [X4,X2,X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f40])).
% 27.71/4.00  
% 27.71/4.00  fof(f7,axiom,(
% 27.71/4.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 27.71/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.71/4.00  
% 27.71/4.00  fof(f14,plain,(
% 27.71/4.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 27.71/4.00    inference(pure_predicate_removal,[],[f7])).
% 27.71/4.00  
% 27.71/4.00  fof(f24,plain,(
% 27.71/4.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.71/4.00    inference(ennf_transformation,[],[f14])).
% 27.71/4.00  
% 27.71/4.00  fof(f25,plain,(
% 27.71/4.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.71/4.00    inference(flattening,[],[f24])).
% 27.71/4.00  
% 27.71/4.00  fof(f62,plain,(
% 27.71/4.00    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f25])).
% 27.71/4.00  
% 27.71/4.00  fof(f77,plain,(
% 27.71/4.00    v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) | v3_pre_topc(sK2,sK1)),
% 27.71/4.00    inference(cnf_transformation,[],[f46])).
% 27.71/4.00  
% 27.71/4.00  fof(f8,axiom,(
% 27.71/4.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 27.71/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.71/4.00  
% 27.71/4.00  fof(f26,plain,(
% 27.71/4.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.71/4.00    inference(ennf_transformation,[],[f8])).
% 27.71/4.00  
% 27.71/4.00  fof(f27,plain,(
% 27.71/4.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.71/4.00    inference(flattening,[],[f26])).
% 27.71/4.00  
% 27.71/4.00  fof(f64,plain,(
% 27.71/4.00    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f27])).
% 27.71/4.00  
% 27.71/4.00  fof(f10,axiom,(
% 27.71/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 27.71/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.71/4.00  
% 27.71/4.00  fof(f30,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.71/4.00    inference(ennf_transformation,[],[f10])).
% 27.71/4.00  
% 27.71/4.00  fof(f31,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.71/4.00    inference(flattening,[],[f30])).
% 27.71/4.00  
% 27.71/4.00  fof(f68,plain,(
% 27.71/4.00    ( ! [X2,X0,X1] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f31])).
% 27.71/4.00  
% 27.71/4.00  fof(f82,plain,(
% 27.71/4.00    ( ! [X2,X0] : (v3_pre_topc(X2,k6_tmap_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.71/4.00    inference(equality_resolution,[],[f68])).
% 27.71/4.00  
% 27.71/4.00  fof(f63,plain,(
% 27.71/4.00    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f27])).
% 27.71/4.00  
% 27.71/4.00  fof(f65,plain,(
% 27.71/4.00    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f27])).
% 27.71/4.00  
% 27.71/4.00  fof(f6,axiom,(
% 27.71/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)))),
% 27.71/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.71/4.00  
% 27.71/4.00  fof(f22,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.71/4.00    inference(ennf_transformation,[],[f6])).
% 27.71/4.00  
% 27.71/4.00  fof(f23,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.71/4.00    inference(flattening,[],[f22])).
% 27.71/4.00  
% 27.71/4.00  fof(f60,plain,(
% 27.71/4.00    ( ! [X0,X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f23])).
% 27.71/4.00  
% 27.71/4.00  fof(f3,axiom,(
% 27.71/4.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 27.71/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.71/4.00  
% 27.71/4.00  fof(f17,plain,(
% 27.71/4.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 27.71/4.00    inference(ennf_transformation,[],[f3])).
% 27.71/4.00  
% 27.71/4.00  fof(f49,plain,(
% 27.71/4.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f17])).
% 27.71/4.00  
% 27.71/4.00  fof(f2,axiom,(
% 27.71/4.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 27.71/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.71/4.00  
% 27.71/4.00  fof(f16,plain,(
% 27.71/4.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 27.71/4.00    inference(ennf_transformation,[],[f2])).
% 27.71/4.00  
% 27.71/4.00  fof(f48,plain,(
% 27.71/4.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f16])).
% 27.71/4.00  
% 27.71/4.00  fof(f53,plain,(
% 27.71/4.00    ( ! [X4,X2,X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f40])).
% 27.71/4.00  
% 27.71/4.00  fof(f78,plain,(
% 27.71/4.00    m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) | v3_pre_topc(sK2,sK1)),
% 27.71/4.00    inference(cnf_transformation,[],[f46])).
% 27.71/4.00  
% 27.71/4.00  fof(f58,plain,(
% 27.71/4.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f40])).
% 27.71/4.00  
% 27.71/4.00  fof(f79,plain,(
% 27.71/4.00    ~m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) | ~v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) | ~v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) | ~v1_funct_1(k7_tmap_1(sK1,sK2)) | ~v3_pre_topc(sK2,sK1)),
% 27.71/4.00    inference(cnf_transformation,[],[f46])).
% 27.71/4.00  
% 27.71/4.00  fof(f11,axiom,(
% 27.71/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 27.71/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.71/4.00  
% 27.71/4.00  fof(f32,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.71/4.00    inference(ennf_transformation,[],[f11])).
% 27.71/4.00  
% 27.71/4.00  fof(f33,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.71/4.00    inference(flattening,[],[f32])).
% 27.71/4.00  
% 27.71/4.00  fof(f41,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.71/4.00    inference(nnf_transformation,[],[f33])).
% 27.71/4.00  
% 27.71/4.00  fof(f69,plain,(
% 27.71/4.00    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f41])).
% 27.71/4.00  
% 27.71/4.00  fof(f4,axiom,(
% 27.71/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 27.71/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.71/4.00  
% 27.71/4.00  fof(f18,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.71/4.00    inference(ennf_transformation,[],[f4])).
% 27.71/4.00  
% 27.71/4.00  fof(f19,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.71/4.00    inference(flattening,[],[f18])).
% 27.71/4.00  
% 27.71/4.00  fof(f36,plain,(
% 27.71/4.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.71/4.00    inference(nnf_transformation,[],[f19])).
% 27.71/4.00  
% 27.71/4.00  fof(f50,plain,(
% 27.71/4.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f36])).
% 27.71/4.00  
% 27.71/4.00  fof(f81,plain,(
% 27.71/4.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.71/4.00    inference(equality_resolution,[],[f50])).
% 27.71/4.00  
% 27.71/4.00  fof(f76,plain,(
% 27.71/4.00    v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) | v3_pre_topc(sK2,sK1)),
% 27.71/4.00    inference(cnf_transformation,[],[f46])).
% 27.71/4.00  
% 27.71/4.00  fof(f56,plain,(
% 27.71/4.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v3_pre_topc(sK0(X0,X1,X2),X1) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f40])).
% 27.71/4.00  
% 27.71/4.00  fof(f57,plain,(
% 27.71/4.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v3_pre_topc(sK0(X0,X1,X2),X1) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f40])).
% 27.71/4.00  
% 27.71/4.00  fof(f54,plain,(
% 27.71/4.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f40])).
% 27.71/4.00  
% 27.71/4.00  fof(f55,plain,(
% 27.71/4.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f40])).
% 27.71/4.00  
% 27.71/4.00  fof(f59,plain,(
% 27.71/4.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.71/4.00    inference(cnf_transformation,[],[f40])).
% 27.71/4.00  
% 27.71/4.00  cnf(c_29,negated_conjecture,
% 27.71/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 27.71/4.00      inference(cnf_transformation,[],[f74]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2473,negated_conjecture,
% 27.71/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_29]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3408,plain,
% 27.71/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2473]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_0,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.71/4.00      | k8_relset_1(X1,X1,k6_partfun1(X1),X0) = X0 ),
% 27.71/4.00      inference(cnf_transformation,[],[f47]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2489,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X0_54))
% 27.71/4.00      | k8_relset_1(X0_54,X0_54,k6_partfun1(X0_54),X0_52) = X0_52 ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_0]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3392,plain,
% 27.71/4.00      ( k8_relset_1(X0_54,X0_54,k6_partfun1(X0_54),X0_52) = X0_52
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(X0_54)) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2489]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3522,plain,
% 27.71/4.00      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK2) = sK2 ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_3408,c_3392]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_20,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.71/4.00      | v2_struct_0(X1)
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 27.71/4.00      inference(cnf_transformation,[],[f66]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_32,negated_conjecture,
% 27.71/4.00      ( ~ v2_struct_0(sK1) ),
% 27.71/4.00      inference(cnf_transformation,[],[f71]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_467,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 27.71/4.00      | sK1 != X1 ),
% 27.71/4.00      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_468,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | ~ v2_pre_topc(sK1)
% 27.71/4.00      | ~ l1_pre_topc(sK1)
% 27.71/4.00      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 27.71/4.00      inference(unflattening,[status(thm)],[c_467]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_31,negated_conjecture,
% 27.71/4.00      ( v2_pre_topc(sK1) ),
% 27.71/4.00      inference(cnf_transformation,[],[f72]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_30,negated_conjecture,
% 27.71/4.00      ( l1_pre_topc(sK1) ),
% 27.71/4.00      inference(cnf_transformation,[],[f73]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_472,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_468,c_31,c_30]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2465,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | u1_struct_0(k6_tmap_1(sK1,X0_52)) = u1_struct_0(sK1) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_472]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3416,plain,
% 27.71/4.00      ( u1_struct_0(k6_tmap_1(sK1,X0_52)) = u1_struct_0(sK1)
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2465]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_5246,plain,
% 27.71/4.00      ( u1_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_3408,c_3416]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_12,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.71/4.00      | ~ v5_pre_topc(X0,X1,X2)
% 27.71/4.00      | ~ v3_pre_topc(X3,X2)
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.71/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 27.71/4.00      | ~ v1_funct_1(X0)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X2)
% 27.71/4.00      | k2_struct_0(X2) = k1_xboole_0 ),
% 27.71/4.00      inference(cnf_transformation,[],[f52]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2479,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | ~ v5_pre_topc(X0_52,X0_55,X1_55)
% 27.71/4.00      | ~ v3_pre_topc(X1_52,X1_55)
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_52,X1_52),X0_55)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X1_55)))
% 27.71/4.00      | ~ v1_funct_1(X0_52)
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | k2_struct_0(X1_55) = k1_xboole_0 ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_12]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3402,plain,
% 27.71/4.00      ( k2_struct_0(X0_55) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(X0_52,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X1_55,X0_55) != iProver_top
% 27.71/4.00      | v3_pre_topc(X1_52,X0_55) != iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X0_55),X0_52,X1_52),X1_55) = iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 27.71/4.00      | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 27.71/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.71/4.00      | l1_pre_topc(X1_55) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2479]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_5413,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(X1_52,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_52,X1_52),X0_55) = iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 27.71/4.00      | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 27.71/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top
% 27.71/4.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_5246,c_3402]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_36,plain,
% 27.71/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_14,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.71/4.00      | v2_struct_0(X1)
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 27.71/4.00      inference(cnf_transformation,[],[f62]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_557,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | l1_pre_topc(k6_tmap_1(X1,X0))
% 27.71/4.00      | sK1 != X1 ),
% 27.71/4.00      inference(resolution_lifted,[status(thm)],[c_14,c_32]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_558,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | ~ v2_pre_topc(sK1)
% 27.71/4.00      | l1_pre_topc(k6_tmap_1(sK1,X0))
% 27.71/4.00      | ~ l1_pre_topc(sK1) ),
% 27.71/4.00      inference(unflattening,[status(thm)],[c_557]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_562,plain,
% 27.71/4.00      ( l1_pre_topc(k6_tmap_1(sK1,X0))
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_558,c_31,c_30]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_563,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | l1_pre_topc(k6_tmap_1(sK1,X0)) ),
% 27.71/4.00      inference(renaming,[status(thm)],[c_562]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2460,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | l1_pre_topc(k6_tmap_1(sK1,X0_52)) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_563]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2611,plain,
% 27.71/4.00      ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | l1_pre_topc(k6_tmap_1(sK1,X0_52)) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2460]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2613,plain,
% 27.71/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2611]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7295,plain,
% 27.71/4.00      ( l1_pre_topc(X0_55) != iProver_top
% 27.71/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.71/4.00      | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_52,X1_52),X0_55) = iProver_top
% 27.71/4.00      | v3_pre_topc(X1_52,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 27.71/4.00      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_5413,c_36,c_2613]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7296,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(X1_52,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_52,X1_52),X0_55) = iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 27.71/4.00      | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 27.71/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top ),
% 27.71/4.00      inference(renaming,[status(thm)],[c_7295]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7305,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(X1_52,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_52,X1_52),X0_55) = iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.00      | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 27.71/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_5246,c_7296]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_38517,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 27.71/4.00      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(sK2,sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 27.71/4.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_3522,c_7305]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_35,plain,
% 27.71/4.00      ( l1_pre_topc(sK1) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_26,negated_conjecture,
% 27.71/4.00      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 27.71/4.00      | v3_pre_topc(sK2,sK1) ),
% 27.71/4.00      inference(cnf_transformation,[],[f77]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_39,plain,
% 27.71/4.00      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2504,plain,
% 27.71/4.00      ( X0_55 != X1_55 | u1_struct_0(X0_55) = u1_struct_0(X1_55) ),
% 27.71/4.00      theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2521,plain,
% 27.71/4.00      ( sK1 != sK1 | u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2504]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2491,plain,( X0_52 = X0_52 ),theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2535,plain,
% 27.71/4.00      ( sK2 = sK2 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2491]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2493,plain,( X0_54 = X0_54 ),theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2537,plain,
% 27.71/4.00      ( k1_xboole_0 = k1_xboole_0 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2493]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2494,plain,( X0_55 = X0_55 ),theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2538,plain,
% 27.71/4.00      ( sK1 = sK1 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2494]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_17,plain,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 27.71/4.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 27.71/4.00      | v2_struct_0(X0)
% 27.71/4.00      | ~ v2_pre_topc(X0)
% 27.71/4.00      | ~ l1_pre_topc(X0) ),
% 27.71/4.00      inference(cnf_transformation,[],[f64]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_386,plain,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 27.71/4.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 27.71/4.00      | ~ v2_pre_topc(X0)
% 27.71/4.00      | ~ l1_pre_topc(X0)
% 27.71/4.00      | sK1 != X0 ),
% 27.71/4.00      inference(resolution_lifted,[status(thm)],[c_17,c_32]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_387,plain,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | ~ v2_pre_topc(sK1)
% 27.71/4.00      | ~ l1_pre_topc(sK1) ),
% 27.71/4.00      inference(unflattening,[status(thm)],[c_386]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_391,plain,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_387,c_31,c_30]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2469,plain,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(sK1,X0_52),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_52)))
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_391]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2584,plain,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(sK1,X0_52),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_52))) = iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2469]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2586,plain,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2584]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_21,plain,
% 27.71/4.00      ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
% 27.71/4.00      | v2_struct_0(X1)
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X1) ),
% 27.71/4.00      inference(cnf_transformation,[],[f82]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_446,plain,
% 27.71/4.00      ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | sK1 != X1 ),
% 27.71/4.00      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_447,plain,
% 27.71/4.00      ( v3_pre_topc(X0,k6_tmap_1(sK1,X0))
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0))))
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | ~ v2_pre_topc(sK1)
% 27.71/4.00      | ~ l1_pre_topc(sK1) ),
% 27.71/4.00      inference(unflattening,[status(thm)],[c_446]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_451,plain,
% 27.71/4.00      ( v3_pre_topc(X0,k6_tmap_1(sK1,X0))
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0))))
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_447,c_31,c_30]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2466,plain,
% 27.71/4.00      ( v3_pre_topc(X0_52,k6_tmap_1(sK1,X0_52))
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_52))))
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_451]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2593,plain,
% 27.71/4.00      ( v3_pre_topc(X0_52,k6_tmap_1(sK1,X0_52)) = iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_52)))) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2466]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2595,plain,
% 27.71/4.00      ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) = iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2593]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2597,plain,
% 27.71/4.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | u1_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2465]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_18,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.71/4.00      | v2_struct_0(X1)
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 27.71/4.00      | ~ l1_pre_topc(X1) ),
% 27.71/4.00      inference(cnf_transformation,[],[f63]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_503,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | sK1 != X1 ),
% 27.71/4.00      inference(resolution_lifted,[status(thm)],[c_18,c_32]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_504,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | ~ v2_pre_topc(sK1)
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,X0))
% 27.71/4.00      | ~ l1_pre_topc(sK1) ),
% 27.71/4.00      inference(unflattening,[status(thm)],[c_503]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_508,plain,
% 27.71/4.00      ( v1_funct_1(k7_tmap_1(sK1,X0))
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_504,c_31,c_30]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_509,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,X0)) ),
% 27.71/4.00      inference(renaming,[status(thm)],[c_508]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2463,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,X0_52)) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_509]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2602,plain,
% 27.71/4.00      ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,X0_52)) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2463]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2604,plain,
% 27.71/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2602]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_16,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.71/4.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 27.71/4.00      | v2_struct_0(X1)
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X1) ),
% 27.71/4.00      inference(cnf_transformation,[],[f65]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_521,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.71/4.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | sK1 != X1 ),
% 27.71/4.00      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_522,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))))
% 27.71/4.00      | ~ v2_pre_topc(sK1)
% 27.71/4.00      | ~ l1_pre_topc(sK1) ),
% 27.71/4.00      inference(unflattening,[status(thm)],[c_521]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_526,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0))))) ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_522,c_31,c_30]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2462,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | m1_subset_1(k7_tmap_1(sK1,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_52))))) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_526]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2605,plain,
% 27.71/4.00      ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | m1_subset_1(k7_tmap_1(sK1,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_52))))) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2462]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2607,plain,
% 27.71/4.00      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2605]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2612,plain,
% 27.71/4.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2460]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_13,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.71/4.00      | v2_struct_0(X1)
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 27.71/4.00      inference(cnf_transformation,[],[f60]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_575,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 27.71/4.00      | sK1 != X1 ),
% 27.71/4.00      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_576,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | ~ v2_pre_topc(sK1)
% 27.71/4.00      | ~ l1_pre_topc(sK1)
% 27.71/4.00      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(unflattening,[status(thm)],[c_575]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_580,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_576,c_31,c_30]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2459,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | k7_tmap_1(sK1,X0_52) = k6_partfun1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_580]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2615,plain,
% 27.71/4.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | k7_tmap_1(sK1,sK2) = k6_partfun1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2459]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2502,plain,
% 27.71/4.00      ( X0_54 != X1_54 | k1_zfmisc_1(X0_54) = k1_zfmisc_1(X1_54) ),
% 27.71/4.00      theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3711,plain,
% 27.71/4.00      ( X0_54 != u1_struct_0(sK1)
% 27.71/4.00      | k1_zfmisc_1(X0_54) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2502]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3890,plain,
% 27.71/4.00      ( u1_struct_0(k6_tmap_1(sK1,X0_52)) != u1_struct_0(sK1)
% 27.71/4.00      | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_52))) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3711]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3891,plain,
% 27.71/4.00      ( u1_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 27.71/4.00      | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3890]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2497,plain,
% 27.71/4.00      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 27.71/4.00      theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3735,plain,
% 27.71/4.00      ( X0_54 != X1_54
% 27.71/4.00      | X0_54 = u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(k6_tmap_1(sK1,sK2)) != X1_54 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2497]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4028,plain,
% 27.71/4.00      ( X0_54 = u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | X0_54 != k2_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(k6_tmap_1(sK1,sK2)) != k2_struct_0(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3735]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4030,plain,
% 27.71/4.00      ( u1_struct_0(k6_tmap_1(sK1,sK2)) != k2_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | k1_xboole_0 = u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_4028]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2,plain,
% 27.71/4.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 27.71/4.00      inference(cnf_transformation,[],[f49]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_1,plain,
% 27.71/4.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 27.71/4.00      inference(cnf_transformation,[],[f48]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_372,plain,
% 27.71/4.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_2,c_1]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2470,plain,
% 27.71/4.00      ( ~ l1_pre_topc(X0_55) | u1_struct_0(X0_55) = k2_struct_0(X0_55) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_372]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4029,plain,
% 27.71/4.00      ( ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2470]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2503,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0_52,X0_53)
% 27.71/4.00      | m1_subset_1(X1_52,X1_53)
% 27.71/4.00      | X1_53 != X0_53
% 27.71/4.00      | X1_52 != X0_52 ),
% 27.71/4.00      theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3561,plain,
% 27.71/4.00      ( m1_subset_1(X0_52,X0_53)
% 27.71/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | X0_53 != k1_zfmisc_1(u1_struct_0(sK1))
% 27.71/4.00      | X0_52 != sK2 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2503]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3710,plain,
% 27.71/4.00      ( m1_subset_1(X0_52,k1_zfmisc_1(X0_54))
% 27.71/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | k1_zfmisc_1(X0_54) != k1_zfmisc_1(u1_struct_0(sK1))
% 27.71/4.00      | X0_52 != sK2 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3561]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4327,plain,
% 27.71/4.00      ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_52))))
% 27.71/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_52))) != k1_zfmisc_1(u1_struct_0(sK1))
% 27.71/4.00      | X0_52 != sK2 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3710]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4328,plain,
% 27.71/4.00      ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_52))) != k1_zfmisc_1(u1_struct_0(sK1))
% 27.71/4.00      | X1_52 != sK2
% 27.71/4.00      | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_52)))) = iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_4327]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4330,plain,
% 27.71/4.00      ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1))
% 27.71/4.00      | sK2 != sK2
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_4328]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4023,plain,
% 27.71/4.00      ( X0_54 = u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | X0_54 != u1_struct_0(sK1)
% 27.71/4.00      | u1_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3735]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4573,plain,
% 27.71/4.00      ( u1_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 27.71/4.00      | u1_struct_0(sK1) = u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_4023]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3886,plain,
% 27.71/4.00      ( k2_struct_0(X0_55) = k2_struct_0(X0_55) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2493]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_5621,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3886]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_5622,plain,
% 27.71/4.00      ( u1_struct_0(k6_tmap_1(sK1,sK2)) != k2_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | k2_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | k2_struct_0(k6_tmap_1(sK1,sK2)) != k2_struct_0(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_4028]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_6503,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 27.71/4.00      | k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,sK2))) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3711]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2500,plain,
% 27.71/4.00      ( X0_54 != X1_54 | k6_partfun1(X0_54) = k6_partfun1(X1_54) ),
% 27.71/4.00      theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4338,plain,
% 27.71/4.00      ( X0_54 != u1_struct_0(sK1)
% 27.71/4.00      | k6_partfun1(X0_54) = k6_partfun1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2500]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_6496,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 27.71/4.00      | k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2))) = k6_partfun1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_4338]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_11,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.71/4.00      | ~ v5_pre_topc(X0,X1,X2)
% 27.71/4.00      | ~ v3_pre_topc(X3,X2)
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.71/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 27.71/4.00      | ~ v1_funct_1(X0)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X2)
% 27.71/4.00      | k2_struct_0(X1) != k1_xboole_0 ),
% 27.71/4.00      inference(cnf_transformation,[],[f53]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2480,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | ~ v5_pre_topc(X0_52,X0_55,X1_55)
% 27.71/4.00      | ~ v3_pre_topc(X1_52,X1_55)
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_52,X1_52),X0_55)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X1_55)))
% 27.71/4.00      | ~ v1_funct_1(X0_52)
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | k2_struct_0(X0_55) != k1_xboole_0 ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_11]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_5293,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X1_52)))
% 27.71/4.00      | ~ v5_pre_topc(X0_52,X0_55,k6_tmap_1(sK1,X1_52))
% 27.71/4.00      | ~ v3_pre_topc(X1_52,k6_tmap_1(sK1,X1_52))
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X1_52)),X0_52,X1_52),X0_55)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X1_52)))))
% 27.71/4.00      | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_52))))
% 27.71/4.00      | ~ v1_funct_1(X0_52)
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(k6_tmap_1(sK1,X1_52))
% 27.71/4.00      | k2_struct_0(X0_55) != k1_xboole_0 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2480]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7050,plain,
% 27.71/4.00      ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X0_52)))
% 27.71/4.00      | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,k6_tmap_1(sK1,X0_52))
% 27.71/4.00      | ~ v3_pre_topc(X0_52,k6_tmap_1(sK1,X0_52))
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X0_52)),k7_tmap_1(sK1,sK2),X0_52),X0_55)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_52))))
% 27.71/4.00      | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X0_52)))))
% 27.71/4.00      | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(k6_tmap_1(sK1,X0_52))
% 27.71/4.00      | k2_struct_0(X0_55) != k1_xboole_0 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_5293]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7051,plain,
% 27.71/4.00      ( k2_struct_0(X0_55) != k1_xboole_0
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X0_52))) != iProver_top
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,k6_tmap_1(sK1,X0_52)) != iProver_top
% 27.71/4.00      | v3_pre_topc(X0_52,k6_tmap_1(sK1,X0_52)) != iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X0_52)),k7_tmap_1(sK1,sK2),X0_52),X0_55) = iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_52)))) != iProver_top
% 27.71/4.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,X0_52))))) != iProver_top
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top
% 27.71/4.00      | l1_pre_topc(k6_tmap_1(sK1,X0_52)) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_7050]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7053,plain,
% 27.71/4.00      ( k2_struct_0(sK1) != k1_xboole_0
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),sK2),sK1) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_7051]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3421,plain,
% 27.71/4.00      ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | l1_pre_topc(k6_tmap_1(sK1,X0_52)) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2460]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7322,plain,
% 27.71/4.00      ( l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_3408,c_3421]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3411,plain,
% 27.71/4.00      ( u1_struct_0(X0_55) = k2_struct_0(X0_55)
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2470]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7448,plain,
% 27.71/4.00      ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_7322,c_3411]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_9232,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_7448,c_5246]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_5203,plain,
% 27.71/4.00      ( X0_54 != X1_54
% 27.71/4.00      | X0_54 = u1_struct_0(X0_55)
% 27.71/4.00      | u1_struct_0(X0_55) != X1_54 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2497]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_10112,plain,
% 27.71/4.00      ( X0_54 = u1_struct_0(X0_55)
% 27.71/4.00      | X0_54 != k2_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(X0_55) != k2_struct_0(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_5203]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_10114,plain,
% 27.71/4.00      ( u1_struct_0(sK1) != k2_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | k1_xboole_0 = u1_struct_0(sK1)
% 27.71/4.00      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_10112]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3917,plain,
% 27.71/4.00      ( m1_subset_1(X0_52,X0_53)
% 27.71/4.00      | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | X0_53 != k1_zfmisc_1(u1_struct_0(sK1))
% 27.71/4.00      | X0_52 != X1_52 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2503]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_12661,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,X2_52))))
% 27.71/4.00      | k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,X2_52))) != k1_zfmisc_1(u1_struct_0(sK1))
% 27.71/4.00      | X1_52 != X0_52 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3917]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_12663,plain,
% 27.71/4.00      ( k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,X0_52))) != k1_zfmisc_1(u1_struct_0(sK1))
% 27.71/4.00      | X1_52 != X2_52
% 27.71/4.00      | m1_subset_1(X2_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,X0_52)))) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_12661]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_12665,plain,
% 27.71/4.00      ( k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1))
% 27.71/4.00      | sK2 != sK2
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_12663]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_5074,plain,
% 27.71/4.00      ( X0_54 != X1_54
% 27.71/4.00      | u1_struct_0(sK1) != X1_54
% 27.71/4.00      | u1_struct_0(sK1) = X0_54 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2497]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_8972,plain,
% 27.71/4.00      ( X0_54 != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(sK1) = X0_54
% 27.71/4.00      | u1_struct_0(sK1) != u1_struct_0(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_5074]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_12687,plain,
% 27.71/4.00      ( u1_struct_0(sK1) != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(sK1) = k2_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | k2_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_8972]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2496,plain,
% 27.71/4.00      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 27.71/4.00      theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4101,plain,
% 27.71/4.00      ( X0_52 != X1_52
% 27.71/4.00      | k7_tmap_1(sK1,X2_52) != X1_52
% 27.71/4.00      | k7_tmap_1(sK1,X2_52) = X0_52 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2496]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_5869,plain,
% 27.71/4.00      ( X0_52 != k6_partfun1(u1_struct_0(sK1))
% 27.71/4.00      | k7_tmap_1(sK1,X1_52) = X0_52
% 27.71/4.00      | k7_tmap_1(sK1,X1_52) != k6_partfun1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_4101]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_12762,plain,
% 27.71/4.00      ( k7_tmap_1(sK1,X0_52) != k6_partfun1(u1_struct_0(sK1))
% 27.71/4.00      | k7_tmap_1(sK1,X0_52) = k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2))) != k6_partfun1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_5869]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_12766,plain,
% 27.71/4.00      ( k7_tmap_1(sK1,sK2) != k6_partfun1(u1_struct_0(sK1))
% 27.71/4.00      | k7_tmap_1(sK1,sK2) = k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2))) != k6_partfun1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_12762]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4317,plain,
% 27.71/4.00      ( X0_52 != X1_52 | X1_52 = X0_52 ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_2496,c_2491]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7213,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X0_54))
% 27.71/4.00      | X0_52 = k8_relset_1(X0_54,X0_54,k6_partfun1(X0_54),X0_52) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_4317,c_2489]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2513,plain,
% 27.71/4.00      ( ~ v3_pre_topc(X0_52,X0_55)
% 27.71/4.00      | v3_pre_topc(X1_52,X1_55)
% 27.71/4.00      | X1_55 != X0_55
% 27.71/4.00      | X1_52 != X0_52 ),
% 27.71/4.00      theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_22360,plain,
% 27.71/4.00      ( v3_pre_topc(X0_52,X0_55)
% 27.71/4.00      | ~ v3_pre_topc(k8_relset_1(X0_54,X0_54,k6_partfun1(X0_54),X0_52),X1_55)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(X0_54))
% 27.71/4.00      | X0_55 != X1_55 ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_7213,c_2513]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_22361,plain,
% 27.71/4.00      ( X0_55 != X1_55
% 27.71/4.00      | v3_pre_topc(X0_52,X0_55) = iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(X0_54,X0_54,k6_partfun1(X0_54),X0_52),X1_55) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(X0_54)) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_22360]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_22363,plain,
% 27.71/4.00      ( sK1 != sK1
% 27.71/4.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2),sK1) != iProver_top
% 27.71/4.00      | v3_pre_topc(sK2,sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_22361]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2476,negated_conjecture,
% 27.71/4.00      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 27.71/4.00      | v3_pre_topc(sK2,sK1) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_26]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3405,plain,
% 27.71/4.00      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2476]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3422,plain,
% 27.71/4.00      ( k7_tmap_1(sK1,X0_52) = k6_partfun1(u1_struct_0(sK1))
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2459]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7776,plain,
% 27.71/4.00      ( k7_tmap_1(sK1,sK2) = k6_partfun1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_3408,c_3422]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_25,negated_conjecture,
% 27.71/4.00      ( v3_pre_topc(sK2,sK1)
% 27.71/4.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
% 27.71/4.00      inference(cnf_transformation,[],[f78]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2477,negated_conjecture,
% 27.71/4.00      ( v3_pre_topc(sK2,sK1)
% 27.71/4.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_25]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3404,plain,
% 27.71/4.00      ( v3_pre_topc(sK2,sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2477]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3648,plain,
% 27.71/4.00      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_3404,c_36,c_2607]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7301,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(X0_52,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k7_tmap_1(sK1,sK2),X0_52),sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_3648,c_7296]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_36429,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(X0_52,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k7_tmap_1(sK1,sK2),X0_52),sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_7301,c_35,c_36,c_2586,c_2604]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_36438,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(X0_52,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),X0_52),sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_7776,c_36429]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_6,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.71/4.00      | v5_pre_topc(X0,X1,X2)
% 27.71/4.00      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.71/4.00      | ~ v1_funct_1(X0)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X2)
% 27.71/4.00      | k2_struct_0(X2) = k1_xboole_0 ),
% 27.71/4.00      inference(cnf_transformation,[],[f58]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2485,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,X1_55)
% 27.71/4.00      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_52,sK0(X0_55,X1_55,X0_52)),X0_55)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | ~ v1_funct_1(X0_52)
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | k2_struct_0(X1_55) = k1_xboole_0 ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_6]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3396,plain,
% 27.71/4.00      ( k2_struct_0(X0_55) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(X0_52,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X1_55,X0_55) = iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X0_55),X0_52,sK0(X1_55,X0_55,X0_52)),X1_55) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 27.71/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.71/4.00      | l1_pre_topc(X1_55) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2485]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_36674,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 27.71/4.00      | k2_struct_0(sK1) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,sK1) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | m1_subset_1(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 27.71/4.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_36438,c_3396]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2582,plain,
% 27.71/4.00      ( ~ l1_pre_topc(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2470]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_24,negated_conjecture,
% 27.71/4.00      ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 27.71/4.00      | ~ v3_pre_topc(sK2,sK1)
% 27.71/4.00      | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
% 27.71/4.00      | ~ v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(cnf_transformation,[],[f79]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2478,negated_conjecture,
% 27.71/4.00      ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 27.71/4.00      | ~ v3_pre_topc(sK2,sK1)
% 27.71/4.00      | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
% 27.71/4.00      | ~ v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_24]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2585,plain,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2469]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2603,plain,
% 27.71/4.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2463]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2606,plain,
% 27.71/4.00      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
% 27.71/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2462]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2674,negated_conjecture,
% 27.71/4.00      ( ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 27.71/4.00      | ~ v3_pre_topc(sK2,sK1) ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_2478,c_29,c_24,c_2585,c_2603,c_2606]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2676,plain,
% 27.71/4.00      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2674]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3888,plain,
% 27.71/4.00      ( k2_struct_0(sK1) = k2_struct_0(sK1) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3886]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4940,plain,
% 27.71/4.00      ( X0_54 != X1_54
% 27.71/4.00      | X0_54 = k2_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | k2_struct_0(k6_tmap_1(sK1,sK2)) != X1_54 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2497]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4941,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) != k1_xboole_0
% 27.71/4.00      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | k1_xboole_0 != k1_xboole_0 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_4940]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3889,plain,
% 27.71/4.00      ( X0_54 != X1_54
% 27.71/4.00      | k2_struct_0(X0_55) != X1_54
% 27.71/4.00      | k2_struct_0(X0_55) = X0_54 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2497]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_5980,plain,
% 27.71/4.00      ( X0_54 != k2_struct_0(X0_55)
% 27.71/4.00      | k2_struct_0(X0_55) = X0_54
% 27.71/4.00      | k2_struct_0(X0_55) != k2_struct_0(X0_55) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3889]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7076,plain,
% 27.71/4.00      ( u1_struct_0(X0_55) != k2_struct_0(X0_55)
% 27.71/4.00      | k2_struct_0(X0_55) = u1_struct_0(X0_55)
% 27.71/4.00      | k2_struct_0(X0_55) != k2_struct_0(X0_55) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_5980]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7077,plain,
% 27.71/4.00      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 27.71/4.00      | k2_struct_0(sK1) = u1_struct_0(sK1)
% 27.71/4.00      | k2_struct_0(sK1) != k2_struct_0(sK1) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_7076]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7083,plain,
% 27.71/4.00      ( k2_struct_0(X0_55) != k2_struct_0(X0_55)
% 27.71/4.00      | k2_struct_0(X0_55) = k2_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | k2_struct_0(k6_tmap_1(sK1,sK2)) != k2_struct_0(X0_55) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_5980]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7085,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) != k2_struct_0(sK1)
% 27.71/4.00      | k2_struct_0(sK1) = k2_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | k2_struct_0(sK1) != k2_struct_0(sK1) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_7083]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3666,plain,
% 27.71/4.00      ( k2_struct_0(X0_55) != X0_54
% 27.71/4.00      | k2_struct_0(X0_55) = k1_xboole_0
% 27.71/4.00      | k1_xboole_0 != X0_54 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2497]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_9770,plain,
% 27.71/4.00      ( k2_struct_0(X0_55) != k2_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | k2_struct_0(X0_55) = k1_xboole_0
% 27.71/4.00      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3666]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_9772,plain,
% 27.71/4.00      ( k2_struct_0(sK1) != k2_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | k2_struct_0(sK1) = k1_xboole_0
% 27.71/4.00      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_9770]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_6532,plain,
% 27.71/4.00      ( X0_54 != X1_54
% 27.71/4.00      | k2_struct_0(k6_tmap_1(sK1,sK2)) != X1_54
% 27.71/4.00      | k2_struct_0(k6_tmap_1(sK1,sK2)) = X0_54 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3889]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_8998,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) != X0_54
% 27.71/4.00      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1)
% 27.71/4.00      | k2_struct_0(sK1) != X0_54 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_6532]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_17915,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 27.71/4.00      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1)
% 27.71/4.00      | k2_struct_0(sK1) != u1_struct_0(sK1) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_8998]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_36669,plain,
% 27.71/4.00      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v3_pre_topc(sK2,sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_3522,c_36438]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_36680,plain,
% 27.71/4.00      ( k2_struct_0(sK1) = k1_xboole_0
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_36674,c_30,c_29,c_36,c_2535,c_2537,c_2582,c_2595,
% 27.71/4.00                 c_2597,c_2676,c_3888,c_3891,c_4330,c_4941,c_7077,c_7085,
% 27.71/4.00                 c_9232,c_9772,c_17915,c_36669]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_36691,plain,
% 27.71/4.00      ( k2_struct_0(sK1) = k1_xboole_0
% 27.71/4.00      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_3405,c_36680]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2501,plain,
% 27.71/4.00      ( X0_54 != X1_54
% 27.71/4.00      | X2_54 != X3_54
% 27.71/4.00      | X0_52 != X1_52
% 27.71/4.00      | X2_52 != X3_52
% 27.71/4.00      | k8_relset_1(X0_54,X2_54,X0_52,X2_52) = k8_relset_1(X1_54,X3_54,X1_52,X3_52) ),
% 27.71/4.00      theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_16074,plain,
% 27.71/4.00      ( ~ v3_pre_topc(k8_relset_1(X0_54,X1_54,X0_52,X1_52),X0_55)
% 27.71/4.00      | v3_pre_topc(k8_relset_1(X2_54,X3_54,X2_52,X3_52),X1_55)
% 27.71/4.00      | X1_55 != X0_55
% 27.71/4.00      | X2_54 != X0_54
% 27.71/4.00      | X3_54 != X1_54
% 27.71/4.00      | X2_52 != X0_52
% 27.71/4.00      | X3_52 != X1_52 ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_2513,c_2501]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_19552,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | ~ v5_pre_topc(X0_52,X0_55,X1_55)
% 27.71/4.00      | ~ v3_pre_topc(X1_52,X1_55)
% 27.71/4.00      | v3_pre_topc(k8_relset_1(X0_54,X1_54,X2_52,X3_52),X2_55)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X1_55)))
% 27.71/4.00      | ~ v1_funct_1(X0_52)
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | X2_55 != X0_55
% 27.71/4.00      | X0_54 != u1_struct_0(X0_55)
% 27.71/4.00      | X1_54 != u1_struct_0(X1_55)
% 27.71/4.00      | k2_struct_0(X1_55) = k1_xboole_0
% 27.71/4.00      | X2_52 != X0_52
% 27.71/4.00      | X3_52 != X1_52 ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_16074,c_2479]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2679,negated_conjecture,
% 27.71/4.00      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_2477,c_29,c_2606]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_39950,plain,
% 27.71/4.00      ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 27.71/4.00      | ~ v3_pre_topc(X0_52,k6_tmap_1(sK1,sK2))
% 27.71/4.00      | v3_pre_topc(k8_relset_1(X0_54,X1_54,X1_52,X2_52),X0_55)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))))
% 27.71/4.00      | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
% 27.71/4.00      | ~ l1_pre_topc(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | ~ l1_pre_topc(sK1)
% 27.71/4.00      | X0_55 != sK1
% 27.71/4.00      | X1_54 != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | X0_54 != u1_struct_0(sK1)
% 27.71/4.00      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 27.71/4.00      | X2_52 != X0_52
% 27.71/4.00      | X1_52 != k7_tmap_1(sK1,sK2) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_19552,c_2679]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2594,plain,
% 27.71/4.00      ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2))
% 27.71/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))))
% 27.71/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2466]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4329,plain,
% 27.71/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))))
% 27.71/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1))
% 27.71/4.00      | sK2 != sK2 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_4327]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_36676,plain,
% 27.71/4.00      ( ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 27.71/4.00      | ~ v3_pre_topc(sK2,k6_tmap_1(sK1,sK2))
% 27.71/4.00      | v3_pre_topc(sK2,sK1)
% 27.71/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))))
% 27.71/4.00      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 27.71/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_36669]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_39988,plain,
% 27.71/4.00      ( ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 27.71/4.00      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_39950,c_37013]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_40004,plain,
% 27.71/4.00      ( v3_pre_topc(sK2,sK1)
% 27.71/4.00      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_39988,c_2476]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4407,plain,
% 27.71/4.00      ( X0_54 != X1_54 | X1_54 = X0_54 ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_2497,c_2493]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_40073,plain,
% 27.71/4.00      ( v3_pre_topc(sK2,sK1)
% 27.71/4.00      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_40004,c_4407]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_40074,plain,
% 27.71/4.00      ( k1_xboole_0 = k2_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_40073]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4318,plain,
% 27.71/4.00      ( X0_54 != X1_54
% 27.71/4.00      | X0_52 != k6_partfun1(X1_54)
% 27.71/4.00      | k6_partfun1(X0_54) = X0_52 ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_2496,c_2500]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_8426,plain,
% 27.71/4.00      ( X0_54 != X1_54
% 27.71/4.00      | X2_54 != X1_54
% 27.71/4.00      | k6_partfun1(X0_54) = k6_partfun1(X2_54) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_4318,c_2500]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_40076,plain,
% 27.71/4.00      ( v3_pre_topc(sK2,sK1)
% 27.71/4.00      | X0_54 != k1_xboole_0
% 27.71/4.00      | k6_partfun1(X0_54) = k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2))) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_40004,c_8426]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_40081,plain,
% 27.71/4.00      ( X0_54 != k1_xboole_0
% 27.71/4.00      | k6_partfun1(X0_54) = k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_40076]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_40083,plain,
% 27.71/4.00      ( k1_xboole_0 != k1_xboole_0
% 27.71/4.00      | k6_partfun1(k1_xboole_0) = k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_40081]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4216,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0_52,X0_53)
% 27.71/4.00      | m1_subset_1(X0_52,X1_53)
% 27.71/4.00      | X1_53 != X0_53 ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_2503,c_2491]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7354,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X0_54))
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(X1_54))
% 27.71/4.00      | X1_54 != X0_54 ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_4216,c_2502]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_40147,plain,
% 27.71/4.00      ( v3_pre_topc(sK2,sK1)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,sK2))))
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_40073,c_7354]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_40156,plain,
% 27.71/4.00      ( v3_pre_topc(sK2,sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_40147]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_40158,plain,
% 27.71/4.00      ( v3_pre_topc(sK2,sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_40156]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3684,plain,
% 27.71/4.00      ( X0_52 != X1_52
% 27.71/4.00      | X0_52 = k7_tmap_1(sK1,sK2)
% 27.71/4.00      | k7_tmap_1(sK1,sK2) != X1_52 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2496]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_38969,plain,
% 27.71/4.00      ( X0_52 = k7_tmap_1(sK1,sK2)
% 27.71/4.00      | X0_52 != k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | k7_tmap_1(sK1,sK2) != k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2))) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3684]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_56891,plain,
% 27.71/4.00      ( k7_tmap_1(sK1,sK2) != k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | k6_partfun1(X0_54) = k7_tmap_1(sK1,sK2)
% 27.71/4.00      | k6_partfun1(X0_54) != k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2))) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_38969]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_56893,plain,
% 27.71/4.00      ( k7_tmap_1(sK1,sK2) != k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | k6_partfun1(k1_xboole_0) = k7_tmap_1(sK1,sK2)
% 27.71/4.00      | k6_partfun1(k1_xboole_0) != k6_partfun1(k2_struct_0(k6_tmap_1(sK1,sK2))) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_56891]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_70936,plain,
% 27.71/4.00      ( X0_54 != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | X1_54 != u1_struct_0(sK1)
% 27.71/4.00      | X0_52 != X1_52
% 27.71/4.00      | X2_52 != k7_tmap_1(sK1,sK2)
% 27.71/4.00      | k8_relset_1(X1_54,X0_54,X2_52,X0_52) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2501]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_72135,plain,
% 27.71/4.00      ( X0_54 != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | X1_54 != u1_struct_0(sK1)
% 27.71/4.00      | X0_52 != X1_52
% 27.71/4.00      | k8_relset_1(X1_54,X0_54,k6_partfun1(X2_54),X0_52) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52)
% 27.71/4.00      | k6_partfun1(X2_54) != k7_tmap_1(sK1,sK2) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_70936]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_72136,plain,
% 27.71/4.00      ( k1_xboole_0 != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | k1_xboole_0 != u1_struct_0(sK1)
% 27.71/4.00      | k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),sK2)
% 27.71/4.00      | k6_partfun1(k1_xboole_0) != k7_tmap_1(sK1,sK2)
% 27.71/4.00      | sK2 != sK2 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_72135]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_70595,plain,
% 27.71/4.00      ( v3_pre_topc(X0_52,X0_55)
% 27.71/4.00      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52),sK1)
% 27.71/4.00      | X0_55 != sK1
% 27.71/4.00      | X0_52 != k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2513]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_70935,plain,
% 27.71/4.00      ( v3_pre_topc(k8_relset_1(X0_54,X1_54,X0_52,X1_52),X0_55)
% 27.71/4.00      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X2_52),sK1)
% 27.71/4.00      | X0_55 != sK1
% 27.71/4.00      | k8_relset_1(X0_54,X1_54,X0_52,X1_52) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X2_52) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_70595]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_76433,plain,
% 27.71/4.00      ( v3_pre_topc(k8_relset_1(X0_54,X1_54,k6_partfun1(X2_54),X0_52),X0_55)
% 27.71/4.00      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52),sK1)
% 27.71/4.00      | X0_55 != sK1
% 27.71/4.00      | k8_relset_1(X0_54,X1_54,k6_partfun1(X2_54),X0_52) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_70935]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_76434,plain,
% 27.71/4.00      ( X0_55 != sK1
% 27.71/4.00      | k8_relset_1(X0_54,X1_54,k6_partfun1(X2_54),X0_52) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52)
% 27.71/4.00      | v3_pre_topc(k8_relset_1(X0_54,X1_54,k6_partfun1(X2_54),X0_52),X0_55) = iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X1_52),sK1) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_76433]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_76436,plain,
% 27.71/4.00      ( sK1 != sK1
% 27.71/4.00      | k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),sK2)
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),sK2),sK1) != iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2),sK1) = iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_76434]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_76751,plain,
% 27.71/4.00      ( v3_pre_topc(sK2,sK1) = iProver_top ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_38517,c_35,c_29,c_36,c_39,c_2521,c_2535,c_2537,c_2538,
% 27.71/4.00                 c_2586,c_2595,c_2597,c_2604,c_2607,c_2612,c_2613,c_2615,
% 27.71/4.00                 c_3891,c_4030,c_4029,c_4330,c_4573,c_5621,c_5622,c_6503,
% 27.71/4.00                 c_6496,c_7053,c_9232,c_10114,c_12665,c_12687,c_12766,
% 27.71/4.00                 c_22363,c_36691,c_40074,c_40083,c_40158,c_56893,c_72136,
% 27.71/4.00                 c_76436]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_23,plain,
% 27.71/4.00      ( ~ v3_pre_topc(X0,X1)
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.71/4.00      | v2_struct_0(X1)
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0) ),
% 27.71/4.00      inference(cnf_transformation,[],[f69]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_404,plain,
% 27.71/4.00      ( ~ v3_pre_topc(X0,X1)
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0)
% 27.71/4.00      | sK1 != X1 ),
% 27.71/4.00      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_405,plain,
% 27.71/4.00      ( ~ v3_pre_topc(X0,sK1)
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | ~ v2_pre_topc(sK1)
% 27.71/4.00      | ~ l1_pre_topc(sK1)
% 27.71/4.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
% 27.71/4.00      inference(unflattening,[status(thm)],[c_404]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_409,plain,
% 27.71/4.00      ( ~ v3_pre_topc(X0,sK1)
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_405,c_31,c_30]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2468,plain,
% 27.71/4.00      ( ~ v3_pre_topc(X0_52,sK1)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0_52) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_409]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3413,plain,
% 27.71/4.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0_52)
% 27.71/4.00      | v3_pre_topc(X0_52,sK1) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2468]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4389,plain,
% 27.71/4.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
% 27.71/4.00      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_3408,c_3413]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_76766,plain,
% 27.71/4.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2) ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_76751,c_4389]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2472,negated_conjecture,
% 27.71/4.00      ( l1_pre_topc(sK1) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_30]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3409,plain,
% 27.71/4.00      ( l1_pre_topc(sK1) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2472]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4060,plain,
% 27.71/4.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_3409,c_3411]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.71/4.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 27.71/4.00      | ~ v5_pre_topc(X0,X1,X2)
% 27.71/4.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 27.71/4.00      | ~ v2_pre_topc(X2)
% 27.71/4.00      | ~ v2_pre_topc(X1)
% 27.71/4.00      | ~ v1_funct_1(X0)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X2) ),
% 27.71/4.00      inference(cnf_transformation,[],[f81]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2487,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))))
% 27.71/4.00      | ~ v5_pre_topc(X0_52,X0_55,X1_55)
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))))))
% 27.71/4.00      | ~ v2_pre_topc(X1_55)
% 27.71/4.00      | ~ v2_pre_topc(X0_55)
% 27.71/4.00      | ~ v1_funct_1(X0_52)
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_4]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3394,plain,
% 27.71/4.00      ( v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 27.71/4.00      | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,X1_55) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) = iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))))) != iProver_top
% 27.71/4.00      | v2_pre_topc(X0_55) != iProver_top
% 27.71/4.00      | v2_pre_topc(X1_55) != iProver_top
% 27.71/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top
% 27.71/4.00      | l1_pre_topc(X1_55) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2487]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_76773,plain,
% 27.71/4.00      ( v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 27.71/4.00      | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,sK1) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.00      | v2_pre_topc(X0_55) != iProver_top
% 27.71/4.00      | v2_pre_topc(sK1) != iProver_top
% 27.71/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top
% 27.71/4.00      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_76766,c_3394]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_34,plain,
% 27.71/4.00      ( v2_pre_topc(sK1) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_76964,plain,
% 27.71/4.00      ( l1_pre_topc(X0_55) != iProver_top
% 27.71/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.71/4.00      | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 27.71/4.00      | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,sK1) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.00      | v2_pre_topc(X0_55) != iProver_top ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_76773,c_34,c_35]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_76965,plain,
% 27.71/4.00      ( v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 27.71/4.00      | v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,sK1) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.00      | v2_pre_topc(X0_55) != iProver_top
% 27.71/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top ),
% 27.71/4.00      inference(renaming,[status(thm)],[c_76964]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_76968,plain,
% 27.71/4.00      ( v1_funct_2(X0_52,u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v1_funct_2(X0_52,k2_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,sK1,sK1) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.00      | v2_pre_topc(sK1) != iProver_top
% 27.71/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.71/4.00      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_4060,c_76965]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_77676,plain,
% 27.71/4.00      ( v1_funct_1(X0_52) != iProver_top
% 27.71/4.00      | v1_funct_2(X0_52,u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v1_funct_2(X0_52,k2_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,sK1,sK1) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_76968,c_34,c_35]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_77677,plain,
% 27.71/4.00      ( v1_funct_2(X0_52,u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v1_funct_2(X0_52,k2_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,sK1,sK1) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.00      | v1_funct_1(X0_52) != iProver_top ),
% 27.71/4.00      inference(renaming,[status(thm)],[c_77676]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_77682,plain,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),k2_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) != iProver_top
% 27.71/4.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_3648,c_77677]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2514,plain,
% 27.71/4.00      ( X0_55 != X1_55
% 27.71/4.00      | X0_52 != X1_52
% 27.71/4.00      | k7_tmap_1(X0_55,X0_52) = k7_tmap_1(X1_55,X1_52) ),
% 27.71/4.00      theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2531,plain,
% 27.71/4.00      ( sK1 != sK1
% 27.71/4.00      | k7_tmap_1(sK1,sK2) = k7_tmap_1(sK1,sK2)
% 27.71/4.00      | sK2 != sK2 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2514]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3925,plain,
% 27.71/4.00      ( X0_52 = k7_tmap_1(sK1,sK2)
% 27.71/4.00      | X0_52 != k6_partfun1(u1_struct_0(sK1))
% 27.71/4.00      | k7_tmap_1(sK1,sK2) != k6_partfun1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3684]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4333,plain,
% 27.71/4.00      ( k7_tmap_1(sK1,sK2) != k6_partfun1(u1_struct_0(sK1))
% 27.71/4.00      | k6_partfun1(u1_struct_0(sK1)) = k7_tmap_1(sK1,sK2)
% 27.71/4.00      | k6_partfun1(u1_struct_0(sK1)) != k6_partfun1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3925]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4334,plain,
% 27.71/4.00      ( k6_partfun1(u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK1)) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2491]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2511,plain,
% 27.71/4.00      ( ~ v1_funct_1(X0_52) | v1_funct_1(X1_52) | X1_52 != X0_52 ),
% 27.71/4.00      theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3539,plain,
% 27.71/4.00      ( v1_funct_1(X0_52)
% 27.71/4.00      | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
% 27.71/4.00      | X0_52 != k7_tmap_1(sK1,sK2) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2511]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4905,plain,
% 27.71/4.00      ( ~ v1_funct_1(k7_tmap_1(sK1,sK2))
% 27.71/4.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
% 27.71/4.00      | k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,sK2) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3539]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4906,plain,
% 27.71/4.00      ( k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,sK2)
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_4905]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_5403,plain,
% 27.71/4.00      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_5246,c_3648]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_27,negated_conjecture,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | v3_pre_topc(sK2,sK1) ),
% 27.71/4.00      inference(cnf_transformation,[],[f76]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2475,negated_conjecture,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | v3_pre_topc(sK2,sK1) ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_27]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3406,plain,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2475]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3625,plain,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_3406,c_36,c_2586]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_5404,plain,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_5246,c_3625]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2506,plain,
% 27.71/4.00      ( ~ v5_pre_topc(X0_52,X0_55,X1_55)
% 27.71/4.00      | v5_pre_topc(X1_52,X2_55,X3_55)
% 27.71/4.00      | X2_55 != X0_55
% 27.71/4.00      | X3_55 != X1_55
% 27.71/4.00      | X1_52 != X0_52 ),
% 27.71/4.00      theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_6117,plain,
% 27.71/4.00      ( v5_pre_topc(k7_tmap_1(sK1,X0_52),X0_55,X1_55)
% 27.71/4.00      | ~ v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X2_55,X3_55)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | X0_55 != X2_55
% 27.71/4.00      | X1_55 != X3_55 ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_2506,c_2459]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_6118,plain,
% 27.71/4.00      ( X0_55 != X1_55
% 27.71/4.00      | X2_55 != X3_55
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,X0_52),X0_55,X2_55) = iProver_top
% 27.71/4.00      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X1_55,X3_55) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_6117]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_6120,plain,
% 27.71/4.00      ( sK1 != sK1
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
% 27.71/4.00      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,sK1) != iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_6118]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2510,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0_52,X0_54,X1_54)
% 27.71/4.00      | v1_funct_2(X1_52,X2_54,X3_54)
% 27.71/4.00      | X2_54 != X0_54
% 27.71/4.00      | X3_54 != X1_54
% 27.71/4.00      | X1_52 != X0_52 ),
% 27.71/4.00      theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3604,plain,
% 27.71/4.00      ( v1_funct_2(X0_52,X0_54,X1_54)
% 27.71/4.00      | ~ v1_funct_2(k7_tmap_1(sK1,X1_52),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1_52)))
% 27.71/4.00      | X1_54 != u1_struct_0(k6_tmap_1(sK1,X1_52))
% 27.71/4.00      | X0_54 != u1_struct_0(sK1)
% 27.71/4.00      | X0_52 != k7_tmap_1(sK1,X1_52) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2510]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3806,plain,
% 27.71/4.00      ( v1_funct_2(X0_52,X0_54,u1_struct_0(X0_55))
% 27.71/4.00      | ~ v1_funct_2(k7_tmap_1(sK1,X1_52),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1_52)))
% 27.71/4.00      | X0_54 != u1_struct_0(sK1)
% 27.71/4.00      | u1_struct_0(X0_55) != u1_struct_0(k6_tmap_1(sK1,X1_52))
% 27.71/4.00      | X0_52 != k7_tmap_1(sK1,X1_52) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3604]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4574,plain,
% 27.71/4.00      ( v1_funct_2(X0_52,u1_struct_0(sK1),u1_struct_0(X0_55))
% 27.71/4.00      | ~ v1_funct_2(k7_tmap_1(sK1,X1_52),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1_52)))
% 27.71/4.00      | u1_struct_0(X0_55) != u1_struct_0(k6_tmap_1(sK1,X1_52))
% 27.71/4.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 27.71/4.00      | X0_52 != k7_tmap_1(sK1,X1_52) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3806]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_6200,plain,
% 27.71/4.00      ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(X0_55))
% 27.71/4.00      | u1_struct_0(X0_55) != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 27.71/4.00      | k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,sK2) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_4574]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_6201,plain,
% 27.71/4.00      ( u1_struct_0(X0_55) != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 27.71/4.00      | k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,sK2)
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 27.71/4.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(X0_55)) = iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_6200]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_6203,plain,
% 27.71/4.00      ( u1_struct_0(sK1) != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 27.71/4.00      | k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,sK2)
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 27.71/4.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_6201]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3914,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),X0_52) = X0_52 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2489]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7045,plain,
% 27.71/4.00      ( ~ m1_subset_1(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))) = sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3914]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7048,plain,
% 27.71/4.00      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))) = sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))
% 27.71/4.00      | m1_subset_1(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_7045]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_6185,plain,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(X0_55,X0_52),u1_struct_0(sK1),u1_struct_0(X1_55))
% 27.71/4.00      | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | u1_struct_0(X1_55) != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 27.71/4.00      | k7_tmap_1(X0_55,X0_52) != k7_tmap_1(sK1,sK2) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_4574]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_8665,plain,
% 27.71/4.00      ( v1_funct_2(k7_tmap_1(X0_55,X0_52),u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))))
% 27.71/4.00      | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 27.71/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 27.71/4.00      | k7_tmap_1(X0_55,X0_52) != k7_tmap_1(sK1,sK2) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_6185]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_8667,plain,
% 27.71/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55))) != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 27.71/4.00      | k7_tmap_1(X1_55,X0_52) != k7_tmap_1(sK1,sK2)
% 27.71/4.00      | v1_funct_2(k7_tmap_1(X1_55,X0_52),u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)))) = iProver_top
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_8665]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_8669,plain,
% 27.71/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 27.71/4.00      | k7_tmap_1(sK1,sK2) != k7_tmap_1(sK1,sK2)
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_8667]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4487,plain,
% 27.71/4.00      ( ~ v3_pre_topc(X0_52,X0_55)
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X2_55),X1_52,sK0(X1_55,X2_55,X1_52)),X1_55)
% 27.71/4.00      | X1_55 != X0_55
% 27.71/4.00      | k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X2_55),X1_52,sK0(X1_55,X2_55,X1_52)) != X0_52 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2513]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_10820,plain,
% 27.71/4.00      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X0_55),k6_partfun1(u1_struct_0(X0_55)),sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55)))),X0_55)
% 27.71/4.00      | ~ v3_pre_topc(sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55))),X1_55)
% 27.71/4.00      | X0_55 != X1_55
% 27.71/4.00      | k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X0_55),k6_partfun1(u1_struct_0(X0_55)),sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55)))) != sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55))) ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_4487]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_10823,plain,
% 27.71/4.00      ( X0_55 != X1_55
% 27.71/4.00      | k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X0_55),k6_partfun1(u1_struct_0(X0_55)),sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55)))) != sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55)))
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X0_55),k6_partfun1(u1_struct_0(X0_55)),sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55)))),X0_55) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK0(X0_55,X0_55,k6_partfun1(u1_struct_0(X0_55))),X1_55) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_10820]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_10825,plain,
% 27.71/4.00      ( sK1 != sK1
% 27.71/4.00      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))) != sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))),sK1) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),sK1) != iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_10823]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_12786,plain,
% 27.71/4.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_7776,c_5403]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_8,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.71/4.00      | v5_pre_topc(X0,X1,X2)
% 27.71/4.00      | v3_pre_topc(sK0(X1,X2,X0),X2)
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.71/4.00      | ~ v1_funct_1(X0)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X2)
% 27.71/4.00      | k2_struct_0(X2) = k1_xboole_0 ),
% 27.71/4.00      inference(cnf_transformation,[],[f56]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2483,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,X1_55)
% 27.71/4.00      | v3_pre_topc(sK0(X0_55,X1_55,X0_52),X1_55)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | ~ v1_funct_1(X0_52)
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | k2_struct_0(X1_55) = k1_xboole_0 ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_8]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3398,plain,
% 27.71/4.00      ( k2_struct_0(X0_55) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(X0_52,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X1_55,X0_55) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK0(X1_55,X0_55,X0_52),X0_55) = iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 27.71/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.71/4.00      | l1_pre_topc(X1_55) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2483]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_12791,plain,
% 27.71/4.00      ( k2_struct_0(sK1) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK0(sK1,sK1,k7_tmap_1(sK1,sK2)),sK1) = iProver_top
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_5403,c_3398]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3615,plain,
% 27.71/4.00      ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,X1_55)
% 27.71/4.00      | v3_pre_topc(sK0(X0_55,X1_55,k7_tmap_1(sK1,sK2)),X1_55)
% 27.71/4.00      | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | k2_struct_0(X1_55) = k1_xboole_0 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2483]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3616,plain,
% 27.71/4.00      ( k2_struct_0(X0_55) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),X1_55,X0_55) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK0(X1_55,X0_55,k7_tmap_1(sK1,sK2)),X0_55) = iProver_top
% 27.71/4.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | l1_pre_topc(X1_55) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_3615]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3618,plain,
% 27.71/4.00      ( k2_struct_0(sK1) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK0(sK1,sK1,k7_tmap_1(sK1,sK2)),sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3616]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_12799,plain,
% 27.71/4.00      ( k2_struct_0(sK1) = k1_xboole_0
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK0(sK1,sK1,k7_tmap_1(sK1,sK2)),sK1) = iProver_top ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_12791,c_35,c_36,c_2604,c_3618,c_5403,c_5404]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_12803,plain,
% 27.71/4.00      ( k2_struct_0(sK1) = k1_xboole_0
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),sK1) = iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_7776,c_12799]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.71/4.00      | v5_pre_topc(X0,X1,X2)
% 27.71/4.00      | v3_pre_topc(sK0(X1,X2,X0),X2)
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.71/4.00      | ~ v1_funct_1(X0)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X2)
% 27.71/4.00      | k2_struct_0(X1) != k1_xboole_0 ),
% 27.71/4.00      inference(cnf_transformation,[],[f57]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2484,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,X1_55)
% 27.71/4.00      | v3_pre_topc(sK0(X0_55,X1_55,X0_52),X1_55)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | ~ v1_funct_1(X0_52)
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | k2_struct_0(X0_55) != k1_xboole_0 ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_7]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7209,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | k6_partfun1(u1_struct_0(sK1)) = k7_tmap_1(sK1,X0_52) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_4317,c_2459]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_7368,plain,
% 27.71/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | ~ m1_subset_1(k7_tmap_1(sK1,X0_52),X0_53)
% 27.71/4.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),X1_53)
% 27.71/4.00      | X1_53 != X0_53 ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_7209,c_2503]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_10685,plain,
% 27.71/4.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),X0_53)
% 27.71/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | X0_53 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_7368,c_2679]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_10700,plain,
% 27.71/4.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),X0_53)
% 27.71/4.00      | X0_53 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))) ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_10685,c_29]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_11146,plain,
% 27.71/4.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(X0_54))
% 27.71/4.00      | X0_54 != k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_10700,c_2502]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2509,plain,
% 27.71/4.00      ( X0_54 != X1_54
% 27.71/4.00      | X2_54 != X3_54
% 27.71/4.00      | k2_zfmisc_1(X0_54,X2_54) = k2_zfmisc_1(X1_54,X3_54) ),
% 27.71/4.00      theory(equality) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_11161,plain,
% 27.71/4.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 27.71/4.00      | X1_54 != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | X0_54 != u1_struct_0(sK1) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_11146,c_2509]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_15306,plain,
% 27.71/4.00      ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X0_55,X1_55)
% 27.71/4.00      | v3_pre_topc(sK0(X0_55,X1_55,k6_partfun1(u1_struct_0(sK1))),X1_55)
% 27.71/4.00      | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | u1_struct_0(X1_55) != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(X0_55) != u1_struct_0(sK1)
% 27.71/4.00      | k2_struct_0(X0_55) != k1_xboole_0 ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_2484,c_11161]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_15307,plain,
% 27.71/4.00      ( u1_struct_0(X0_55) != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 27.71/4.00      | k2_struct_0(X1_55) != k1_xboole_0
% 27.71/4.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
% 27.71/4.00      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X1_55,X0_55) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK0(X1_55,X0_55,k6_partfun1(u1_struct_0(sK1))),X0_55) = iProver_top
% 27.71/4.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | l1_pre_topc(X1_55) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_15306]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_15309,plain,
% 27.71/4.00      ( u1_struct_0(sK1) != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 27.71/4.00      | k2_struct_0(sK1) != k1_xboole_0
% 27.71/4.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,sK1) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),sK1) = iProver_top
% 27.71/4.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_15307]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_19078,plain,
% 27.71/4.00      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
% 27.71/4.00      | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),sK1) = iProver_top ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_12803,c_35,c_29,c_36,c_2521,c_2538,c_2586,c_2597,
% 27.71/4.00                 c_2604,c_2615,c_4333,c_4334,c_4573,c_4906,c_6120,c_6203,
% 27.71/4.00                 c_15309]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_10,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.71/4.00      | v5_pre_topc(X0,X1,X2)
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.71/4.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 27.71/4.00      | ~ v1_funct_1(X0)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X2)
% 27.71/4.00      | k2_struct_0(X2) = k1_xboole_0 ),
% 27.71/4.00      inference(cnf_transformation,[],[f54]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2481,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,X1_55)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | m1_subset_1(sK0(X0_55,X1_55,X0_52),k1_zfmisc_1(u1_struct_0(X1_55)))
% 27.71/4.00      | ~ v1_funct_1(X0_52)
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | k2_struct_0(X1_55) = k1_xboole_0 ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_10]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3400,plain,
% 27.71/4.00      ( k2_struct_0(X0_55) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(X0_52,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
% 27.71/4.00      | v5_pre_topc(X0_52,X1_55,X0_55) = iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 27.71/4.00      | m1_subset_1(sK0(X1_55,X0_55,X0_52),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 27.71/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.71/4.00      | l1_pre_topc(X1_55) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_2481]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_12790,plain,
% 27.71/4.00      ( k2_struct_0(sK1) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(sK0(sK1,sK1,k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_5403,c_3400]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3607,plain,
% 27.71/4.00      ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,X1_55)
% 27.71/4.00      | m1_subset_1(sK0(X0_55,X1_55,k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(X1_55)))
% 27.71/4.00      | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | k2_struct_0(X1_55) = k1_xboole_0 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2481]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3608,plain,
% 27.71/4.00      ( k2_struct_0(X0_55) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),X1_55,X0_55) = iProver_top
% 27.71/4.00      | m1_subset_1(sK0(X1_55,X0_55,k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 27.71/4.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | l1_pre_topc(X1_55) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_3607]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_3610,plain,
% 27.71/4.00      ( k2_struct_0(sK1) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(sK0(sK1,sK1,k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 27.71/4.00      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.00      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.00      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_3608]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_13005,plain,
% 27.71/4.00      ( k2_struct_0(sK1) = k1_xboole_0
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(sK0(sK1,sK1,k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 27.71/4.00      inference(global_propositional_subsumption,
% 27.71/4.00                [status(thm)],
% 27.71/4.00                [c_12790,c_35,c_36,c_2604,c_3610,c_5403,c_5404]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_13009,plain,
% 27.71/4.00      ( k2_struct_0(sK1) = k1_xboole_0
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_7776,c_13005]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_21839,plain,
% 27.71/4.00      ( k2_struct_0(sK1) = k1_xboole_0
% 27.71/4.00      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))) = sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))
% 27.71/4.00      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) = iProver_top ),
% 27.71/4.00      inference(superposition,[status(thm)],[c_13009,c_3392]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_4408,plain,
% 27.71/4.00      ( X0_55 != X1_55
% 27.71/4.00      | X0_54 != u1_struct_0(X1_55)
% 27.71/4.00      | u1_struct_0(X0_55) = X0_54 ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_2497,c_2504]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_8442,plain,
% 27.71/4.00      ( X0_55 != X1_55
% 27.71/4.00      | X2_55 != X1_55
% 27.71/4.00      | u1_struct_0(X0_55) = u1_struct_0(X2_55) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_4408,c_2504]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_25516,plain,
% 27.71/4.00      ( ~ v3_pre_topc(X0_52,sK1)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | X0_55 != k6_tmap_1(sK1,X0_52)
% 27.71/4.00      | u1_struct_0(X0_55) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_8442,c_2468]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_25808,plain,
% 27.71/4.00      ( ~ v3_pre_topc(X0_52,sK1)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | u1_struct_0(k6_tmap_1(sK1,X0_52)) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_25516,c_2494]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_27784,plain,
% 27.71/4.00      ( ~ v3_pre_topc(X0_52,sK1)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 27.71/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(k6_tmap_1(sK1,X0_52)) ),
% 27.71/4.00      inference(resolution,[status(thm)],[c_25808,c_4407]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_27785,plain,
% 27.71/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(k6_tmap_1(sK1,X0_52))
% 27.71/4.00      | v3_pre_topc(X0_52,sK1) != iProver_top
% 27.71/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_27784]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_27787,plain,
% 27.71/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.00      | v3_pre_topc(sK2,sK1) != iProver_top
% 27.71/4.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_27785]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_9,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.71/4.00      | v5_pre_topc(X0,X1,X2)
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.71/4.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 27.71/4.00      | ~ v1_funct_1(X0)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X2)
% 27.71/4.00      | k2_struct_0(X1) != k1_xboole_0 ),
% 27.71/4.00      inference(cnf_transformation,[],[f55]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2482,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,X1_55)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | m1_subset_1(sK0(X0_55,X1_55,X0_52),k1_zfmisc_1(u1_struct_0(X1_55)))
% 27.71/4.00      | ~ v1_funct_1(X0_52)
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | k2_struct_0(X0_55) != k1_xboole_0 ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_9]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_34401,plain,
% 27.71/4.00      ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X0_55,X1_55)
% 27.71/4.00      | m1_subset_1(sK0(X0_55,X1_55,k6_partfun1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(X1_55)))
% 27.71/4.00      | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | k2_struct_0(X0_55) != k1_xboole_0 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2482]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_34402,plain,
% 27.71/4.00      ( k2_struct_0(X0_55) != k1_xboole_0
% 27.71/4.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 27.71/4.00      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X0_55,X1_55) = iProver_top
% 27.71/4.00      | m1_subset_1(sK0(X0_55,X1_55,k6_partfun1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(X1_55))) = iProver_top
% 27.71/4.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 27.71/4.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top
% 27.71/4.00      | l1_pre_topc(X1_55) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_34401]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_34404,plain,
% 27.71/4.00      ( k2_struct_0(sK1) != k1_xboole_0
% 27.71/4.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,sK1) = iProver_top
% 27.71/4.00      | m1_subset_1(sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 27.71/4.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_34402]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_38106,plain,
% 27.71/4.00      ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X0_55,X1_55)
% 27.71/4.00      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),k6_partfun1(u1_struct_0(sK1)),sK0(X0_55,X1_55,k6_partfun1(u1_struct_0(sK1)))),X0_55)
% 27.71/4.00      | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | k2_struct_0(X1_55) = k1_xboole_0 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2485]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_38111,plain,
% 27.71/4.00      ( k2_struct_0(X0_55) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
% 27.71/4.00      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X1_55,X0_55) = iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X0_55),k6_partfun1(u1_struct_0(sK1)),sK0(X1_55,X0_55,k6_partfun1(u1_struct_0(sK1)))),X1_55) != iProver_top
% 27.71/4.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 27.71/4.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | l1_pre_topc(X1_55) != iProver_top
% 27.71/4.00      | l1_pre_topc(X0_55) != iProver_top ),
% 27.71/4.00      inference(predicate_to_equality,[status(thm)],[c_38106]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_38113,plain,
% 27.71/4.00      ( k2_struct_0(sK1) = k1_xboole_0
% 27.71/4.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 27.71/4.00      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,sK1) = iProver_top
% 27.71/4.00      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))),sK1) != iProver_top
% 27.71/4.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.00      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_38111]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_5,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.71/4.00      | v5_pre_topc(X0,X1,X2)
% 27.71/4.00      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 27.71/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.71/4.00      | ~ v1_funct_1(X0)
% 27.71/4.00      | ~ l1_pre_topc(X1)
% 27.71/4.00      | ~ l1_pre_topc(X2)
% 27.71/4.00      | k2_struct_0(X1) != k1_xboole_0 ),
% 27.71/4.00      inference(cnf_transformation,[],[f59]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_2486,plain,
% 27.71/4.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | v5_pre_topc(X0_52,X0_55,X1_55)
% 27.71/4.00      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_52,sK0(X0_55,X1_55,X0_52)),X0_55)
% 27.71/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | ~ v1_funct_1(X0_52)
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | k2_struct_0(X0_55) != k1_xboole_0 ),
% 27.71/4.00      inference(subtyping,[status(esa)],[c_5]) ).
% 27.71/4.00  
% 27.71/4.00  cnf(c_38105,plain,
% 27.71/4.00      ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.00      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X0_55,X1_55)
% 27.71/4.00      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),k6_partfun1(u1_struct_0(sK1)),sK0(X0_55,X1_55,k6_partfun1(u1_struct_0(sK1)))),X0_55)
% 27.71/4.00      | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.00      | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
% 27.71/4.00      | ~ l1_pre_topc(X0_55)
% 27.71/4.00      | ~ l1_pre_topc(X1_55)
% 27.71/4.00      | k2_struct_0(X0_55) != k1_xboole_0 ),
% 27.71/4.00      inference(instantiation,[status(thm)],[c_2486]) ).
% 27.71/4.01  
% 27.71/4.01  cnf(c_38115,plain,
% 27.71/4.01      ( k2_struct_0(X0_55) != k1_xboole_0
% 27.71/4.01      | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 27.71/4.01      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),X0_55,X1_55) = iProver_top
% 27.71/4.01      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),k6_partfun1(u1_struct_0(sK1)),sK0(X0_55,X1_55,k6_partfun1(u1_struct_0(sK1)))),X0_55) != iProver_top
% 27.71/4.01      | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 27.71/4.01      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.01      | l1_pre_topc(X0_55) != iProver_top
% 27.71/4.01      | l1_pre_topc(X1_55) != iProver_top ),
% 27.71/4.01      inference(predicate_to_equality,[status(thm)],[c_38105]) ).
% 27.71/4.01  
% 27.71/4.01  cnf(c_38117,plain,
% 27.71/4.01      ( k2_struct_0(sK1) != k1_xboole_0
% 27.71/4.01      | v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 27.71/4.01      | v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,sK1) = iProver_top
% 27.71/4.01      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK0(sK1,sK1,k6_partfun1(u1_struct_0(sK1)))),sK1) != iProver_top
% 27.71/4.01      | m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.01      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
% 27.71/4.01      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.01      inference(instantiation,[status(thm)],[c_38115]) ).
% 27.71/4.01  
% 27.71/4.01  cnf(c_22400,plain,
% 27.71/4.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 27.71/4.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54)))
% 27.71/4.01      | X2_54 != X0_54
% 27.71/4.01      | X3_54 != X1_54 ),
% 27.71/4.01      inference(resolution,[status(thm)],[c_7354,c_2509]) ).
% 27.71/4.01  
% 27.71/4.01  cnf(c_59293,plain,
% 27.71/4.01      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 27.71/4.01      | X1_54 != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.01      | X0_54 != u1_struct_0(sK1) ),
% 27.71/4.01      inference(resolution,[status(thm)],[c_22400,c_2679]) ).
% 27.71/4.01  
% 27.71/4.01  cnf(c_59551,plain,
% 27.71/4.01      ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(X1_55))
% 27.71/4.01      | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))))
% 27.71/4.01      | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,X1_55)
% 27.71/4.01      | v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))
% 27.71/4.01      | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 27.71/4.01      | ~ v2_pre_topc(X1_55)
% 27.71/4.01      | ~ v2_pre_topc(X0_55)
% 27.71/4.01      | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
% 27.71/4.01      | ~ l1_pre_topc(X0_55)
% 27.71/4.01      | ~ l1_pre_topc(X1_55)
% 27.71/4.01      | u1_struct_0(X0_55) != u1_struct_0(sK1)
% 27.71/4.01      | u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) != u1_struct_0(k6_tmap_1(sK1,sK2)) ),
% 27.71/4.01      inference(resolution,[status(thm)],[c_59293,c_2487]) ).
% 27.71/4.01  
% 27.71/4.01  cnf(c_59556,plain,
% 27.71/4.01      ( u1_struct_0(X0_55) != u1_struct_0(sK1)
% 27.71/4.01      | u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.01      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 27.71/4.01      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(X0_55),u1_struct_0(g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))) != iProver_top
% 27.71/4.01      | v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,X1_55) != iProver_top
% 27.71/4.01      | v5_pre_topc(k7_tmap_1(sK1,sK2),X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) = iProver_top
% 27.71/4.01      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 27.71/4.01      | v2_pre_topc(X0_55) != iProver_top
% 27.71/4.01      | v2_pre_topc(X1_55) != iProver_top
% 27.71/4.01      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.01      | l1_pre_topc(X0_55) != iProver_top
% 27.71/4.01      | l1_pre_topc(X1_55) != iProver_top ),
% 27.71/4.01      inference(predicate_to_equality,[status(thm)],[c_59551]) ).
% 27.71/4.01  
% 27.71/4.01  cnf(c_59558,plain,
% 27.71/4.01      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != u1_struct_0(k6_tmap_1(sK1,sK2))
% 27.71/4.01      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 27.71/4.01      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 27.71/4.01      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 27.71/4.01      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 27.71/4.01      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) != iProver_top
% 27.71/4.01      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 27.71/4.01      | v2_pre_topc(sK1) != iProver_top
% 27.71/4.01      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.01      | l1_pre_topc(sK1) != iProver_top ),
% 27.71/4.01      inference(instantiation,[status(thm)],[c_59556]) ).
% 27.71/4.01  
% 27.71/4.01  cnf(c_78090,plain,
% 27.71/4.01      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 27.71/4.01      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) != iProver_top ),
% 27.71/4.01      inference(global_propositional_subsumption,
% 27.71/4.01                [status(thm)],
% 27.71/4.01                [c_77682,c_34,c_35,c_29,c_36,c_39,c_2521,c_2531,c_2535,
% 27.71/4.01                 c_2537,c_2538,c_2586,c_2595,c_2597,c_2604,c_2607,c_2612,
% 27.71/4.01                 c_2613,c_2615,c_3891,c_4030,c_4029,c_4330,c_4333,c_4334,
% 27.71/4.01                 c_4573,c_4906,c_5403,c_5404,c_5621,c_5622,c_6120,c_6203,
% 27.71/4.01                 c_6503,c_6496,c_7048,c_7053,c_8669,c_9232,c_10114,
% 27.71/4.01                 c_10825,c_12665,c_12687,c_12766,c_12786,c_19078,c_21839,
% 27.71/4.01                 c_22363,c_27787,c_34404,c_36691,c_38113,c_38117,c_40074,
% 27.71/4.01                 c_40083,c_40158,c_56893,c_59558,c_72136,c_76436]) ).
% 27.71/4.01  
% 27.71/4.01  cnf(c_78096,plain,
% 27.71/4.01      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 27.71/4.01      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,sK1) != iProver_top ),
% 27.71/4.01      inference(superposition,[status(thm)],[c_76766,c_78090]) ).
% 27.71/4.01  
% 27.71/4.01  cnf(c_41,plain,
% 27.71/4.01      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 27.71/4.01      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 27.71/4.01      | v3_pre_topc(sK2,sK1) != iProver_top
% 27.71/4.01      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 27.71/4.01      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top ),
% 27.71/4.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.71/4.01  
% 27.71/4.01  cnf(contradiction,plain,
% 27.71/4.01      ( $false ),
% 27.71/4.01      inference(minisat,
% 27.71/4.01                [status(thm)],
% 27.71/4.01                [c_78096,c_76751,c_38117,c_38113,c_34404,c_21839,c_19078,
% 27.71/4.01                 c_12786,c_10825,c_7048,c_6203,c_6120,c_4906,c_4573,
% 27.71/4.01                 c_4334,c_4333,c_2615,c_2607,c_2604,c_2597,c_2586,c_2538,
% 27.71/4.01                 c_2521,c_41,c_36,c_29,c_35]) ).
% 27.71/4.01  
% 27.71/4.01  
% 27.71/4.01  % SZS output end CNFRefutation for theBenchmark.p
% 27.71/4.01  
% 27.71/4.01  ------                               Statistics
% 27.71/4.01  
% 27.71/4.01  ------ Selected
% 27.71/4.01  
% 27.71/4.01  total_time:                             3.228
% 27.71/4.01  
%------------------------------------------------------------------------------
