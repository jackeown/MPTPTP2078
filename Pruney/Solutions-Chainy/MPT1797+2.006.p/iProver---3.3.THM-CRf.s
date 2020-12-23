%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:00 EST 2020

% Result     : Theorem 51.67s
% Output     : CNFRefutation 51.67s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2844)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f74,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v3_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v3_pre_topc(sK0(X0,X1,X2),X1)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f83,plain,
    ( v1_funct_1(k7_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
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
    inference(equality_resolution,[],[f57])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v3_pre_topc(sK0(X0,X1,X2),X1)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2781,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_3761,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2781])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2800,plain,
    ( ~ l1_pre_topc(X0_55)
    | l1_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3742,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | l1_struct_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2800])).

cnf(c_4348,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3761,c_3742])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2801,plain,
    ( ~ l1_struct_0(X0_55)
    | u1_struct_0(X0_55) = k2_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3741,plain,
    ( u1_struct_0(X0_55) = k2_struct_0(X0_55)
    | l1_struct_0(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2801])).

cnf(c_4459,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_4348,c_3741])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2782,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_3760,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2782])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_35])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_34,c_33])).

cnf(c_2775,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0_53)) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_492])).

cnf(c_3767,plain,
    ( u1_struct_0(k6_tmap_1(sK1,X0_53)) = u1_struct_0(sK1)
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2775])).

cnf(c_4951,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_3760,c_3767])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f60])).

cnf(c_2788,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v5_pre_topc(X0_53,X0_55,X1_55)
    | ~ v3_pre_topc(X1_53,X1_55)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,X1_53),X0_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ v1_funct_1(X0_53)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | k2_struct_0(X1_55) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3754,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,X1_55,X0_55) != iProver_top
    | v3_pre_topc(X1_53,X0_55) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X0_55),X0_53,X1_53),X1_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2788])).

cnf(c_5649,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,X1_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4951,c_3754])).

cnf(c_5661,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,X1_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5649,c_4951])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_577,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_35])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | l1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_582,plain,
    ( l1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_578,c_34,c_33])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | l1_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_582])).

cnf(c_2770,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
    | l1_pre_topc(k6_tmap_1(sK1,X0_53)) ),
    inference(subtyping,[status(esa)],[c_583])).

cnf(c_2932,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2770])).

cnf(c_2934,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2932])).

cnf(c_12936,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,X1_53),X0_55) = iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5661,c_39,c_2934])).

cnf(c_12937,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,X1_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_12936])).

cnf(c_12942,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,X1_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12937,c_4459])).

cnf(c_6401,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_4459,c_4951])).

cnf(c_3772,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2770])).

cnf(c_4696,plain,
    ( l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3760,c_3772])).

cnf(c_4700,plain,
    ( l1_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4696,c_3742])).

cnf(c_6887,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_4700,c_3741])).

cnf(c_8164,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_6401,c_6887])).

cnf(c_12943,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,X1_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12942,c_8164])).

cnf(c_12956,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4459,c_12943])).

cnf(c_12978,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12956,c_4459])).

cnf(c_6493,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
    | v3_pre_topc(X1_53,X0_55) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4459,c_3754])).

cnf(c_6762,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
    | v3_pre_topc(X1_53,X0_55) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6493,c_4459])).

cnf(c_38,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_18954,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
    | v3_pre_topc(X1_53,X0_55) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | k2_struct_0(X0_55) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6762,c_38])).

cnf(c_18955,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
    | v3_pre_topc(X1_53,X0_55) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_18954])).

cnf(c_18968,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6401,c_18955])).

cnf(c_18979,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18968,c_6401])).

cnf(c_18980,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18979,c_8164])).

cnf(c_22898,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,X1_53),sK1) = iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12978,c_38])).

cnf(c_22899,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_22898])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2794,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_53,X0_55,X1_55)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,sK0(X0_55,X1_55,X0_53)),X0_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(X0_53)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | k2_struct_0(X1_55) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3748,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,X1_55,X0_55) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X0_55),X0_53,sK0(X1_55,X0_55,X0_53)),X1_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2794])).

cnf(c_6501,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,sK0(X0_55,sK1,X0_53)),X0_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4459,c_3748])).

cnf(c_6610,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,sK0(X0_55,sK1,X0_53)),X0_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6501,c_4459])).

cnf(c_16109,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,sK0(X0_55,sK1,X0_53)),X0_55) != iProver_top
    | v5_pre_topc(X0_53,X0_55,sK1) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6610,c_38])).

cnf(c_16110,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,sK0(X0_55,sK1,X0_53)),X0_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_16109])).

cnf(c_16121,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,sK1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(sK1,sK1,X0_53)),sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4459,c_16110])).

cnf(c_16145,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,sK1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(sK1,sK1,X0_53)),sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16121,c_4459])).

cnf(c_16602,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(sK1,sK1,X0_53)),sK1) != iProver_top
    | v5_pre_topc(X0_53,sK1,sK1) = iProver_top
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16145,c_38])).

cnf(c_16603,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,sK1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(sK1,sK1,X0_53)),sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_16602])).

cnf(c_22915,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_53,sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,X0_53),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK1,X0_53),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_22899,c_16603])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_595,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_35])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_600,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_596,c_34,c_33])).

cnf(c_2769,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,X0_53) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_600])).

cnf(c_3773,plain,
    ( k7_tmap_1(sK1,X0_53) = k6_partfun1(u1_struct_0(sK1))
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2769])).

cnf(c_5285,plain,
    ( k7_tmap_1(sK1,sK2) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_3760,c_3773])).

cnf(c_6399,plain,
    ( k7_tmap_1(sK1,sK2) = k6_partfun1(k2_struct_0(sK1)) ),
    inference(demodulation,[status(thm)],[c_4459,c_5285])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_35])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_34,c_33])).

cnf(c_2772,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))))) ),
    inference(subtyping,[status(esa)],[c_546])).

cnf(c_3770,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2772])).

cnf(c_6393,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,X0_53),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4459,c_3770])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v3_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2792,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_53,X0_55,X1_55)
    | v3_pre_topc(sK0(X0_55,X1_55,X0_53),X1_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(X0_53)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | k2_struct_0(X1_55) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3750,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,X1_55,X0_55) = iProver_top
    | v3_pre_topc(sK0(X1_55,X0_55,X0_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2792])).

cnf(c_5008,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4951,c_3750])).

cnf(c_5133,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5008,c_4951])).

cnf(c_11271,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | k2_struct_0(X0_55) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5133,c_39,c_2934])).

cnf(c_11272,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_11271])).

cnf(c_11277,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11272,c_4459])).

cnf(c_11288,plain,
    ( k2_struct_0(k6_tmap_1(sK1,X0_53)) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,X0_53),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53)),k6_tmap_1(sK1,X0_53)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_53)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6393,c_11277])).

cnf(c_20,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_406,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_35])).

cnf(c_407,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_411,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_407,c_34,c_33])).

cnf(c_2779,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_53),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_411])).

cnf(c_3763,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_53),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2779])).

cnf(c_6394,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_53),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4459,c_3763])).

cnf(c_6403,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_53)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4459,c_3772])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_524,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k7_tmap_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_528,plain,
    ( v1_funct_1(k7_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_34,c_33])).

cnf(c_529,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_528])).

cnf(c_2773,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,X0_53)) ),
    inference(subtyping,[status(esa)],[c_529])).

cnf(c_3769,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2773])).

cnf(c_6405,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_53)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4459,c_3769])).

cnf(c_22469,plain,
    ( k2_struct_0(k6_tmap_1(sK1,X0_53)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53)),k6_tmap_1(sK1,X0_53)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11288,c_6394,c_6403,c_6405])).

cnf(c_22479,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6399,c_22469])).

cnf(c_22480,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22479,c_6399])).

cnf(c_22481,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22480,c_8164])).

cnf(c_6407,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4459,c_3760])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k8_relset_1(X1,X1,k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2802,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | k8_relset_1(X1_53,X1_53,k6_partfun1(X1_53),X0_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3740,plain,
    ( k8_relset_1(X0_53,X0_53,k6_partfun1(X0_53),X1_53) = X1_53
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2802])).

cnf(c_4359,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_3760,c_3740])).

cnf(c_6406,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_4459,c_4359])).

cnf(c_22913,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6406,c_22899])).

cnf(c_2805,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2847,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2805])).

cnf(c_24,plain,
    ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_466,plain,
    ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_467,plain,
    ( v3_pre_topc(X0,k6_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_471,plain,
    ( v3_pre_topc(X0,k6_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_34,c_33])).

cnf(c_2776,plain,
    ( v3_pre_topc(X0_53,k6_tmap_1(sK1,X0_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_53))))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_471])).

cnf(c_2914,plain,
    ( v3_pre_topc(X0_53,k6_tmap_1(sK1,X0_53)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_53)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2776])).

cnf(c_2916,plain,
    ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2914])).

cnf(c_2918,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_2814,plain,
    ( k1_zfmisc_1(X0_53) = k1_zfmisc_1(X1_53)
    | X0_53 != X1_53 ),
    theory(equality)).

cnf(c_4393,plain,
    ( k1_zfmisc_1(X0_53) = k1_zfmisc_1(u1_struct_0(sK1))
    | X0_53 != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2814])).

cnf(c_4580,plain,
    ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_53))) = k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(k6_tmap_1(sK1,X0_53)) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4393])).

cnf(c_4581,plain,
    ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) = k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4580])).

cnf(c_2815,plain,
    ( ~ m1_subset_1(X0_53,X0_54)
    | m1_subset_1(X1_53,X1_54)
    | X1_54 != X0_54
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_4203,plain,
    ( m1_subset_1(X0_53,X0_54)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_54 != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_53 != sK2 ),
    inference(instantiation,[status(thm)],[c_2815])).

cnf(c_4392,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_zfmisc_1(X1_53) != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_53 != sK2 ),
    inference(instantiation,[status(thm)],[c_4203])).

cnf(c_4953,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_53))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_53))) != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_53 != sK2 ),
    inference(instantiation,[status(thm)],[c_4392])).

cnf(c_4954,plain,
    ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_53))) != k1_zfmisc_1(u1_struct_0(sK1))
    | X1_53 != sK2
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_53)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4953])).

cnf(c_4956,plain,
    ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4954])).

cnf(c_31,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2783,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_3759,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2783])).

cnf(c_2923,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2773])).

cnf(c_2925,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2923])).

cnf(c_4188,plain,
    ( v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3759,c_39,c_2925])).

cnf(c_5369,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5285,c_4188])).

cnf(c_6398,plain,
    ( v1_funct_1(k6_partfun1(k2_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4459,c_5369])).

cnf(c_29,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2785,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_3757,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2785])).

cnf(c_5368,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5285,c_3757])).

cnf(c_7270,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5368,c_4459])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2784,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | v3_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_3758,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2784])).

cnf(c_2905,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_53),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2779])).

cnf(c_2907,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2905])).

cnf(c_4257,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3758,c_39,c_2907])).

cnf(c_5000,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4951,c_4257])).

cnf(c_5367,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5285,c_5000])).

cnf(c_8551,plain,
    ( v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5367,c_4459])).

cnf(c_28,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2786,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_3756,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2786])).

cnf(c_2926,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2772])).

cnf(c_2928,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2926])).

cnf(c_4263,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3756,c_39,c_2928])).

cnf(c_4999,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4951,c_4263])).

cnf(c_5366,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5285,c_4999])).

cnf(c_8614,plain,
    ( m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5366,c_4459])).

cnf(c_23131,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22913,c_32,c_39,c_2847,c_2916,c_2918,c_4581,c_4956,c_6398,c_6407,c_7270,c_8551,c_8614])).

cnf(c_23132,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_23131])).

cnf(c_26,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_424,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_425,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_429,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_425,c_34,c_33])).

cnf(c_2778,plain,
    ( ~ v3_pre_topc(X0_53,sK1)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0_53) ),
    inference(subtyping,[status(esa)],[c_429])).

cnf(c_3764,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0_53)
    | v3_pre_topc(X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2778])).

cnf(c_6148,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3760,c_3764])).

cnf(c_6391,plain,
    ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4459,c_6148])).

cnf(c_23142,plain,
    ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_23132,c_6391])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2799,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55))),u1_struct_0(X1_55))
    | v5_pre_topc(X0_53,X0_55,X1_55)
    | ~ v5_pre_topc(X0_53,g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)),X1_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55))),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ v1_funct_1(X0_53)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3743,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55))),u1_struct_0(X1_55)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,X1_55) = iProver_top
    | v5_pre_topc(X0_53,g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)),X1_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55))),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2799])).

cnf(c_6505,plain,
    ( v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4459,c_3743])).

cnf(c_6533,plain,
    ( v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6505,c_4459])).

cnf(c_37,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_13941,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6533,c_37,c_38])).

cnf(c_13942,plain,
    ( v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_13941])).

cnf(c_23172,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_23142,c_13942])).

cnf(c_23226,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23172,c_6401])).

cnf(c_24639,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_23142,c_23226])).

cnf(c_24671,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24639,c_6401])).

cnf(c_24966,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,X0_53),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,X0_53)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),sK1,k6_tmap_1(sK1,X0_53)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,X0_53)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_53)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6393,c_24671])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(k6_tmap_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_564,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_560,c_34,c_33])).

cnf(c_2771,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(k6_tmap_1(sK1,X0_53)) ),
    inference(subtyping,[status(esa)],[c_564])).

cnf(c_3771,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2771])).

cnf(c_6404,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,X0_53)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4459,c_3771])).

cnf(c_27474,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),sK1,k6_tmap_1(sK1,X0_53)) = iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,X0_53)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24966,c_6394,c_6403,c_6404,c_6405])).

cnf(c_27475,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,X0_53)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),sK1,k6_tmap_1(sK1,X0_53)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_27474])).

cnf(c_27485,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6399,c_27475])).

cnf(c_27499,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27485,c_6399])).

cnf(c_27,negated_conjecture,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2787,negated_conjecture,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3755,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2787])).

cnf(c_2906,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2779])).

cnf(c_2924,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2773])).

cnf(c_2927,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2772])).

cnf(c_3004,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2787,c_32,c_27,c_2906,c_2924,c_2927])).

cnf(c_3006,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3004])).

cnf(c_4164,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3755,c_3006])).

cnf(c_5370,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5285,c_4164])).

cnf(c_6395,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4459,c_5370])).

cnf(c_27509,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27499,c_2844,c_2847,c_2849,c_6395,c_6407,c_23289])).

cnf(c_27516,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23142,c_27509])).

cnf(c_48688,plain,
    ( v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22481,c_6407,c_27516])).

cnf(c_48689,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_48688])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2790,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_53,X0_55,X1_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | m1_subset_1(sK0(X0_55,X1_55,X0_53),k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ v1_funct_1(X0_53)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | k2_struct_0(X1_55) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3752,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,X1_55,X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(sK0(X1_55,X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2790])).

cnf(c_5007,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4951,c_3752])).

cnf(c_5150,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5007,c_4951])).

cnf(c_11346,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | k2_struct_0(X0_55) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5150,c_39,c_2934])).

cnf(c_11347,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_11346])).

cnf(c_11352,plain,
    ( k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11347,c_4459])).

cnf(c_11365,plain,
    ( k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X0_55),k6_partfun1(u1_struct_0(X0_55)),sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)) = sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)
    | k2_struct_0(X0_55) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_11352,c_3740])).

cnf(c_11855,plain,
    ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_53)),u1_struct_0(k6_tmap_1(sK1,X0_53)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_53))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53))
    | k2_struct_0(k6_tmap_1(sK1,X0_53)) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,X0_53),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_53)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6393,c_11365])).

cnf(c_24154,plain,
    ( k2_struct_0(k6_tmap_1(sK1,X0_53)) = k1_xboole_0
    | k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_53)),u1_struct_0(k6_tmap_1(sK1,X0_53)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_53))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53))
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11855,c_6394,c_6403,c_6405])).

cnf(c_24155,plain,
    ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_53)),u1_struct_0(k6_tmap_1(sK1,X0_53)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_53))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53))
    | k2_struct_0(k6_tmap_1(sK1,X0_53)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_24154])).

cnf(c_24164,plain,
    ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(sK1,sK2)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,sK2))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6399,c_24155])).

cnf(c_24165,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24164,c_6399,c_6401])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2803,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3739,plain,
    ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2803])).

cnf(c_4343,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X0_53) = k10_relat_1(k7_tmap_1(sK1,sK2),X0_53) ),
    inference(superposition,[status(thm)],[c_4263,c_3739])).

cnf(c_5840,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),X0_53) = k10_relat_1(k6_partfun1(u1_struct_0(sK1)),X0_53) ),
    inference(light_normalisation,[status(thm)],[c_4343,c_4951,c_5285])).

cnf(c_6396,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),X0_53) = k10_relat_1(k6_partfun1(k2_struct_0(sK1)),X0_53) ),
    inference(demodulation,[status(thm)],[c_4459,c_5840])).

cnf(c_24166,plain,
    ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
    | k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24165,c_6396,c_8164])).

cnf(c_5011,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4951,c_3752])).

cnf(c_5078,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5011,c_4951])).

cnf(c_10342,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5078,c_39,c_2934])).

cnf(c_10343,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_10342])).

cnf(c_10348,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10343,c_4459])).

cnf(c_10359,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)) = sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_10348,c_3740])).

cnf(c_10771,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)) = sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8164,c_10359])).

cnf(c_21161,plain,
    ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)) = sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10771,c_6396])).

cnf(c_21173,plain,
    ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6401,c_21161])).

cnf(c_21181,plain,
    ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21173,c_6401])).

cnf(c_22038,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0
    | k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21181,c_39,c_2934])).

cnf(c_22039,plain,
    ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_22038])).

cnf(c_22050,plain,
    ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8614,c_22039])).

cnf(c_51518,plain,
    ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24166,c_6398,c_8551,c_22050,c_27516])).

cnf(c_5504,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)),X0_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4951,c_3748])).

cnf(c_5513,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)),X0_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5504,c_4951])).

cnf(c_11551,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)),X0_55) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5513,c_39,c_2934])).

cnf(c_11552,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)),X0_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_11551])).

cnf(c_11557,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)),X0_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11552,c_4459])).

cnf(c_11558,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)),X0_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11557,c_8164])).

cnf(c_11570,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6401,c_11558])).

cnf(c_11578,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11570,c_6401])).

cnf(c_22023,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11578,c_39,c_2934])).

cnf(c_22024,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_22023])).

cnf(c_22035,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6396,c_22024])).

cnf(c_67163,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22035,c_6398,c_8551,c_8614,c_27516])).

cnf(c_67169,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_51518,c_67163])).

cnf(c_67326,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22915,c_48689,c_67169])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v3_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2793,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_53,X0_55,X1_55)
    | v3_pre_topc(sK0(X0_55,X1_55,X0_53),X1_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(X0_53)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | k2_struct_0(X0_55) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3749,plain,
    ( k2_struct_0(X0_55) != k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,X1_55) = iProver_top
    | v3_pre_topc(sK0(X0_55,X1_55,X0_53),X1_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2793])).

cnf(c_10850,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8164,c_3749])).

cnf(c_10875,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10850,c_6401])).

cnf(c_18118,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10875,c_39,c_2934])).

cnf(c_18119,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_18118])).

cnf(c_67501,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_18119])).

cnf(c_68135,plain,
    ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_67501])).

cnf(c_67562,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_67326,c_6401])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2791,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_53,X0_55,X1_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | m1_subset_1(sK0(X0_55,X1_55,X0_53),k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ v1_funct_1(X0_53)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | k2_struct_0(X0_55) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3751,plain,
    ( k2_struct_0(X0_55) != k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,X1_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(sK0(X0_55,X1_55,X0_53),k1_zfmisc_1(u1_struct_0(X1_55))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2791])).

cnf(c_10849,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8164,c_3751])).

cnf(c_10892,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10849,c_6401])).

cnf(c_21645,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10892,c_39,c_2934])).

cnf(c_21646,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_21645])).

cnf(c_67481,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_21646])).

cnf(c_68166,plain,
    ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_67481])).

cnf(c_90027,plain,
    ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_67562,c_68166])).

cnf(c_90061,plain,
    ( v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_90027,c_67562])).

cnf(c_91184,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_90061,c_39,c_2934])).

cnf(c_91185,plain,
    ( v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_91184])).

cnf(c_91195,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)
    | v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_91185,c_3740])).

cnf(c_67531,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X0_53) = k10_relat_1(k6_partfun1(k1_xboole_0),X0_53) ),
    inference(demodulation,[status(thm)],[c_67326,c_6396])).

cnf(c_91358,plain,
    ( k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)
    | v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(demodulation,[status(thm)],[c_91195,c_67531])).

cnf(c_67563,plain,
    ( k7_tmap_1(sK1,sK2) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_67326,c_6399])).

cnf(c_67548,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,X0_53),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,X0_53))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_6393])).

cnf(c_67518,plain,
    ( v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)),X0_55) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_13942])).

cnf(c_67560,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_67326,c_6406])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_2789,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v5_pre_topc(X0_53,X0_55,X1_55)
    | ~ v3_pre_topc(X1_53,X1_55)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,X1_53),X0_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ v1_funct_1(X0_53)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | k2_struct_0(X0_55) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3753,plain,
    ( k2_struct_0(X0_55) != k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,X1_55) != iProver_top
    | v3_pre_topc(X1_53,X1_55) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,X1_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X1_55))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2789])).

cnf(c_68327,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
    | v3_pre_topc(X1_53,X0_55) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_67326,c_3753])).

cnf(c_70702,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
    | v3_pre_topc(X1_53,X0_55) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_68327,c_38])).

cnf(c_70703,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
    | v3_pre_topc(X1_53,X0_55) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_70702])).

cnf(c_67571,plain,
    ( u1_struct_0(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_67326,c_4459])).

cnf(c_70706,plain,
    ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
    | v3_pre_topc(X1_53,X0_55) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_70703,c_67571])).

cnf(c_70719,plain,
    ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_67562,c_70706])).

cnf(c_70729,plain,
    ( v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_70719,c_67562])).

cnf(c_73465,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,X1_53),sK1) = iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_70729,c_39,c_2934])).

cnf(c_73466,plain,
    ( v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,X1_53),sK1) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_73465])).

cnf(c_73479,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_67560,c_73466])).

cnf(c_67559,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_8614])).

cnf(c_67561,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_8551])).

cnf(c_67567,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_6398])).

cnf(c_67568,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_7270])).

cnf(c_67570,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_6407])).

cnf(c_73624,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_73479,c_32,c_39,c_2847,c_2916,c_2918,c_4581,c_4956,c_67559,c_67561,c_67567,c_67568,c_67570])).

cnf(c_67554,plain,
    ( g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_6391])).

cnf(c_73629,plain,
    ( g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_73624,c_67554])).

cnf(c_74842,plain,
    ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) != iProver_top
    | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_67518,c_67562,c_73629])).

cnf(c_74853,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_53),k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,X0_53))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),sK1,k6_tmap_1(sK1,X0_53)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,X0_53)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_53)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_67548,c_74842])).

cnf(c_67549,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_53),k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,X0_53))) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_6394])).

cnf(c_67556,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_53)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_6405])).

cnf(c_67557,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,X0_53)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_6404])).

cnf(c_67558,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_53)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_6403])).

cnf(c_74959,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),sK1,k6_tmap_1(sK1,X0_53)) = iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_74853,c_67549,c_67556,c_67557,c_67558])).

cnf(c_74960,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_53),sK1,k6_tmap_1(sK1,X0_53)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_74959])).

cnf(c_74970,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_67563,c_74960])).

cnf(c_74974,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_74970,c_67563])).

cnf(c_67550,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_6395])).

cnf(c_74980,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_74974,c_32,c_39,c_2847,c_2916,c_2918,c_4581,c_4956,c_67550,c_67559,c_67561,c_67567,c_67568,c_67570,c_73479])).

cnf(c_93202,plain,
    ( k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))
    | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_91358,c_74980])).

cnf(c_95107,plain,
    ( k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_93202,c_67559,c_67561,c_67567])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2795,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_53,X0_55,X1_55)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,sK0(X0_55,X1_55,X0_53)),X0_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v1_funct_1(X0_53)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | k2_struct_0(X0_55) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3747,plain,
    ( k2_struct_0(X0_55) != k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v5_pre_topc(X0_53,X0_55,X1_55) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,sK0(X0_55,X1_55,X0_53)),X0_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2795])).

cnf(c_10848,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55),X0_53,sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8164,c_3747])).

cnf(c_10909,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_55),X0_53,sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10848,c_6401])).

cnf(c_13481,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_55),X0_53,sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10909,c_39,c_2934])).

cnf(c_13482,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_55),X0_53,sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_13481])).

cnf(c_67524,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_55),X0_53,sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(demodulation,[status(thm)],[c_67326,c_13482])).

cnf(c_67873,plain,
    ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_55),X0_53,sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_67524])).

cnf(c_85373,plain,
    ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_67562,c_67873])).

cnf(c_85394,plain,
    ( v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_85373,c_67562])).

cnf(c_85509,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_85394,c_39,c_2934])).

cnf(c_85510,plain,
    ( v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_85509])).

cnf(c_85520,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_67531,c_85510])).

cnf(c_85523,plain,
    ( v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))),k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_85520,c_32,c_39,c_2847,c_2916,c_2918,c_4581,c_4956,c_67550,c_67559,c_67561,c_67567,c_67568,c_67570,c_73479,c_74974])).

cnf(c_95110,plain,
    ( v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_95107,c_85523])).

cnf(c_158357,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_68135,c_95110])).

cnf(c_158358,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_158357,c_67562])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_158358,c_74974,c_73624,c_67570,c_67567,c_67561,c_67559,c_67550,c_2934,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:52:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 51.67/7.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.67/7.03  
% 51.67/7.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.67/7.03  
% 51.67/7.03  ------  iProver source info
% 51.67/7.03  
% 51.67/7.03  git: date: 2020-06-30 10:37:57 +0100
% 51.67/7.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.67/7.03  git: non_committed_changes: false
% 51.67/7.03  git: last_make_outside_of_git: false
% 51.67/7.03  
% 51.67/7.03  ------ 
% 51.67/7.03  
% 51.67/7.03  ------ Input Options
% 51.67/7.03  
% 51.67/7.03  --out_options                           all
% 51.67/7.03  --tptp_safe_out                         true
% 51.67/7.03  --problem_path                          ""
% 51.67/7.03  --include_path                          ""
% 51.67/7.03  --clausifier                            res/vclausify_rel
% 51.67/7.03  --clausifier_options                    --mode clausify
% 51.67/7.03  --stdin                                 false
% 51.67/7.03  --stats_out                             all
% 51.67/7.03  
% 51.67/7.03  ------ General Options
% 51.67/7.03  
% 51.67/7.03  --fof                                   false
% 51.67/7.03  --time_out_real                         305.
% 51.67/7.03  --time_out_virtual                      -1.
% 51.67/7.03  --symbol_type_check                     false
% 51.67/7.03  --clausify_out                          false
% 51.67/7.03  --sig_cnt_out                           false
% 51.67/7.03  --trig_cnt_out                          false
% 51.67/7.03  --trig_cnt_out_tolerance                1.
% 51.67/7.03  --trig_cnt_out_sk_spl                   false
% 51.67/7.03  --abstr_cl_out                          false
% 51.67/7.03  
% 51.67/7.03  ------ Global Options
% 51.67/7.03  
% 51.67/7.03  --schedule                              default
% 51.67/7.03  --add_important_lit                     false
% 51.67/7.03  --prop_solver_per_cl                    1000
% 51.67/7.03  --min_unsat_core                        false
% 51.67/7.03  --soft_assumptions                      false
% 51.67/7.03  --soft_lemma_size                       3
% 51.67/7.03  --prop_impl_unit_size                   0
% 51.67/7.03  --prop_impl_unit                        []
% 51.67/7.03  --share_sel_clauses                     true
% 51.67/7.03  --reset_solvers                         false
% 51.67/7.03  --bc_imp_inh                            [conj_cone]
% 51.67/7.03  --conj_cone_tolerance                   3.
% 51.67/7.03  --extra_neg_conj                        none
% 51.67/7.03  --large_theory_mode                     true
% 51.67/7.03  --prolific_symb_bound                   200
% 51.67/7.03  --lt_threshold                          2000
% 51.67/7.03  --clause_weak_htbl                      true
% 51.67/7.03  --gc_record_bc_elim                     false
% 51.67/7.03  
% 51.67/7.03  ------ Preprocessing Options
% 51.67/7.03  
% 51.67/7.03  --preprocessing_flag                    true
% 51.67/7.03  --time_out_prep_mult                    0.1
% 51.67/7.03  --splitting_mode                        input
% 51.67/7.03  --splitting_grd                         true
% 51.67/7.03  --splitting_cvd                         false
% 51.67/7.03  --splitting_cvd_svl                     false
% 51.67/7.03  --splitting_nvd                         32
% 51.67/7.03  --sub_typing                            true
% 51.67/7.03  --prep_gs_sim                           true
% 51.67/7.03  --prep_unflatten                        true
% 51.67/7.03  --prep_res_sim                          true
% 51.67/7.03  --prep_upred                            true
% 51.67/7.03  --prep_sem_filter                       exhaustive
% 51.67/7.03  --prep_sem_filter_out                   false
% 51.67/7.03  --pred_elim                             true
% 51.67/7.03  --res_sim_input                         true
% 51.67/7.03  --eq_ax_congr_red                       true
% 51.67/7.03  --pure_diseq_elim                       true
% 51.67/7.03  --brand_transform                       false
% 51.67/7.03  --non_eq_to_eq                          false
% 51.67/7.03  --prep_def_merge                        true
% 51.67/7.03  --prep_def_merge_prop_impl              false
% 51.67/7.03  --prep_def_merge_mbd                    true
% 51.67/7.03  --prep_def_merge_tr_red                 false
% 51.67/7.03  --prep_def_merge_tr_cl                  false
% 51.67/7.03  --smt_preprocessing                     true
% 51.67/7.03  --smt_ac_axioms                         fast
% 51.67/7.03  --preprocessed_out                      false
% 51.67/7.03  --preprocessed_stats                    false
% 51.67/7.03  
% 51.67/7.03  ------ Abstraction refinement Options
% 51.67/7.03  
% 51.67/7.03  --abstr_ref                             []
% 51.67/7.03  --abstr_ref_prep                        false
% 51.67/7.03  --abstr_ref_until_sat                   false
% 51.67/7.03  --abstr_ref_sig_restrict                funpre
% 51.67/7.03  --abstr_ref_af_restrict_to_split_sk     false
% 51.67/7.03  --abstr_ref_under                       []
% 51.67/7.03  
% 51.67/7.03  ------ SAT Options
% 51.67/7.03  
% 51.67/7.03  --sat_mode                              false
% 51.67/7.03  --sat_fm_restart_options                ""
% 51.67/7.03  --sat_gr_def                            false
% 51.67/7.03  --sat_epr_types                         true
% 51.67/7.03  --sat_non_cyclic_types                  false
% 51.67/7.03  --sat_finite_models                     false
% 51.67/7.03  --sat_fm_lemmas                         false
% 51.67/7.03  --sat_fm_prep                           false
% 51.67/7.03  --sat_fm_uc_incr                        true
% 51.67/7.03  --sat_out_model                         small
% 51.67/7.03  --sat_out_clauses                       false
% 51.67/7.03  
% 51.67/7.03  ------ QBF Options
% 51.67/7.03  
% 51.67/7.03  --qbf_mode                              false
% 51.67/7.03  --qbf_elim_univ                         false
% 51.67/7.03  --qbf_dom_inst                          none
% 51.67/7.03  --qbf_dom_pre_inst                      false
% 51.67/7.03  --qbf_sk_in                             false
% 51.67/7.03  --qbf_pred_elim                         true
% 51.67/7.03  --qbf_split                             512
% 51.67/7.03  
% 51.67/7.03  ------ BMC1 Options
% 51.67/7.03  
% 51.67/7.03  --bmc1_incremental                      false
% 51.67/7.03  --bmc1_axioms                           reachable_all
% 51.67/7.03  --bmc1_min_bound                        0
% 51.67/7.03  --bmc1_max_bound                        -1
% 51.67/7.03  --bmc1_max_bound_default                -1
% 51.67/7.03  --bmc1_symbol_reachability              true
% 51.67/7.03  --bmc1_property_lemmas                  false
% 51.67/7.03  --bmc1_k_induction                      false
% 51.67/7.03  --bmc1_non_equiv_states                 false
% 51.67/7.03  --bmc1_deadlock                         false
% 51.67/7.03  --bmc1_ucm                              false
% 51.67/7.03  --bmc1_add_unsat_core                   none
% 51.67/7.03  --bmc1_unsat_core_children              false
% 51.67/7.03  --bmc1_unsat_core_extrapolate_axioms    false
% 51.67/7.03  --bmc1_out_stat                         full
% 51.67/7.03  --bmc1_ground_init                      false
% 51.67/7.03  --bmc1_pre_inst_next_state              false
% 51.67/7.03  --bmc1_pre_inst_state                   false
% 51.67/7.03  --bmc1_pre_inst_reach_state             false
% 51.67/7.03  --bmc1_out_unsat_core                   false
% 51.67/7.03  --bmc1_aig_witness_out                  false
% 51.67/7.03  --bmc1_verbose                          false
% 51.67/7.03  --bmc1_dump_clauses_tptp                false
% 51.67/7.03  --bmc1_dump_unsat_core_tptp             false
% 51.67/7.03  --bmc1_dump_file                        -
% 51.67/7.03  --bmc1_ucm_expand_uc_limit              128
% 51.67/7.03  --bmc1_ucm_n_expand_iterations          6
% 51.67/7.03  --bmc1_ucm_extend_mode                  1
% 51.67/7.03  --bmc1_ucm_init_mode                    2
% 51.67/7.03  --bmc1_ucm_cone_mode                    none
% 51.67/7.03  --bmc1_ucm_reduced_relation_type        0
% 51.67/7.03  --bmc1_ucm_relax_model                  4
% 51.67/7.03  --bmc1_ucm_full_tr_after_sat            true
% 51.67/7.03  --bmc1_ucm_expand_neg_assumptions       false
% 51.67/7.03  --bmc1_ucm_layered_model                none
% 51.67/7.03  --bmc1_ucm_max_lemma_size               10
% 51.67/7.03  
% 51.67/7.03  ------ AIG Options
% 51.67/7.03  
% 51.67/7.03  --aig_mode                              false
% 51.67/7.03  
% 51.67/7.03  ------ Instantiation Options
% 51.67/7.03  
% 51.67/7.03  --instantiation_flag                    true
% 51.67/7.03  --inst_sos_flag                         false
% 51.67/7.03  --inst_sos_phase                        true
% 51.67/7.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.67/7.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.67/7.03  --inst_lit_sel_side                     num_symb
% 51.67/7.03  --inst_solver_per_active                1400
% 51.67/7.03  --inst_solver_calls_frac                1.
% 51.67/7.03  --inst_passive_queue_type               priority_queues
% 51.67/7.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.67/7.03  --inst_passive_queues_freq              [25;2]
% 51.67/7.03  --inst_dismatching                      true
% 51.67/7.03  --inst_eager_unprocessed_to_passive     true
% 51.67/7.03  --inst_prop_sim_given                   true
% 51.67/7.03  --inst_prop_sim_new                     false
% 51.67/7.03  --inst_subs_new                         false
% 51.67/7.03  --inst_eq_res_simp                      false
% 51.67/7.03  --inst_subs_given                       false
% 51.67/7.03  --inst_orphan_elimination               true
% 51.67/7.03  --inst_learning_loop_flag               true
% 51.67/7.03  --inst_learning_start                   3000
% 51.67/7.03  --inst_learning_factor                  2
% 51.67/7.03  --inst_start_prop_sim_after_learn       3
% 51.67/7.03  --inst_sel_renew                        solver
% 51.67/7.03  --inst_lit_activity_flag                true
% 51.67/7.03  --inst_restr_to_given                   false
% 51.67/7.03  --inst_activity_threshold               500
% 51.67/7.03  --inst_out_proof                        true
% 51.67/7.03  
% 51.67/7.03  ------ Resolution Options
% 51.67/7.03  
% 51.67/7.03  --resolution_flag                       true
% 51.67/7.03  --res_lit_sel                           adaptive
% 51.67/7.03  --res_lit_sel_side                      none
% 51.67/7.03  --res_ordering                          kbo
% 51.67/7.03  --res_to_prop_solver                    active
% 51.67/7.03  --res_prop_simpl_new                    false
% 51.67/7.03  --res_prop_simpl_given                  true
% 51.67/7.03  --res_passive_queue_type                priority_queues
% 51.67/7.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.67/7.03  --res_passive_queues_freq               [15;5]
% 51.67/7.03  --res_forward_subs                      full
% 51.67/7.03  --res_backward_subs                     full
% 51.67/7.03  --res_forward_subs_resolution           true
% 51.67/7.03  --res_backward_subs_resolution          true
% 51.67/7.03  --res_orphan_elimination                true
% 51.67/7.03  --res_time_limit                        2.
% 51.67/7.03  --res_out_proof                         true
% 51.67/7.03  
% 51.67/7.03  ------ Superposition Options
% 51.67/7.03  
% 51.67/7.03  --superposition_flag                    true
% 51.67/7.03  --sup_passive_queue_type                priority_queues
% 51.67/7.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.67/7.03  --sup_passive_queues_freq               [8;1;4]
% 51.67/7.03  --demod_completeness_check              fast
% 51.67/7.03  --demod_use_ground                      true
% 51.67/7.03  --sup_to_prop_solver                    passive
% 51.67/7.03  --sup_prop_simpl_new                    true
% 51.67/7.03  --sup_prop_simpl_given                  true
% 51.67/7.03  --sup_fun_splitting                     false
% 51.67/7.03  --sup_smt_interval                      50000
% 51.67/7.03  
% 51.67/7.03  ------ Superposition Simplification Setup
% 51.67/7.03  
% 51.67/7.03  --sup_indices_passive                   []
% 51.67/7.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.67/7.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.67/7.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.67/7.03  --sup_full_triv                         [TrivRules;PropSubs]
% 51.67/7.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.67/7.03  --sup_full_bw                           [BwDemod]
% 51.67/7.03  --sup_immed_triv                        [TrivRules]
% 51.67/7.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.67/7.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.67/7.03  --sup_immed_bw_main                     []
% 51.67/7.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.67/7.03  --sup_input_triv                        [Unflattening;TrivRules]
% 51.67/7.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.67/7.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.67/7.03  
% 51.67/7.03  ------ Combination Options
% 51.67/7.03  
% 51.67/7.03  --comb_res_mult                         3
% 51.67/7.03  --comb_sup_mult                         2
% 51.67/7.03  --comb_inst_mult                        10
% 51.67/7.03  
% 51.67/7.03  ------ Debug Options
% 51.67/7.03  
% 51.67/7.03  --dbg_backtrace                         false
% 51.67/7.03  --dbg_dump_prop_clauses                 false
% 51.67/7.03  --dbg_dump_prop_clauses_file            -
% 51.67/7.03  --dbg_out_stat                          false
% 51.67/7.03  ------ Parsing...
% 51.67/7.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.67/7.03  
% 51.67/7.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 51.67/7.03  
% 51.67/7.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.67/7.03  
% 51.67/7.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.67/7.03  ------ Proving...
% 51.67/7.03  ------ Problem Properties 
% 51.67/7.03  
% 51.67/7.03  
% 51.67/7.03  clauses                                 35
% 51.67/7.03  conjectures                             8
% 51.67/7.03  EPR                                     3
% 51.67/7.03  Horn                                    24
% 51.67/7.03  unary                                   3
% 51.67/7.03  binary                                  16
% 51.67/7.03  lits                                    153
% 51.67/7.03  lits eq                                 20
% 51.67/7.03  fd_pure                                 0
% 51.67/7.03  fd_pseudo                               0
% 51.67/7.03  fd_cond                                 0
% 51.67/7.03  fd_pseudo_cond                          0
% 51.67/7.03  AC symbols                              0
% 51.67/7.03  
% 51.67/7.03  ------ Schedule dynamic 5 is on 
% 51.67/7.03  
% 51.67/7.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.67/7.03  
% 51.67/7.03  
% 51.67/7.03  ------ 
% 51.67/7.03  Current options:
% 51.67/7.03  ------ 
% 51.67/7.03  
% 51.67/7.03  ------ Input Options
% 51.67/7.03  
% 51.67/7.03  --out_options                           all
% 51.67/7.03  --tptp_safe_out                         true
% 51.67/7.03  --problem_path                          ""
% 51.67/7.03  --include_path                          ""
% 51.67/7.03  --clausifier                            res/vclausify_rel
% 51.67/7.03  --clausifier_options                    --mode clausify
% 51.67/7.03  --stdin                                 false
% 51.67/7.03  --stats_out                             all
% 51.67/7.03  
% 51.67/7.03  ------ General Options
% 51.67/7.03  
% 51.67/7.03  --fof                                   false
% 51.67/7.03  --time_out_real                         305.
% 51.67/7.03  --time_out_virtual                      -1.
% 51.67/7.03  --symbol_type_check                     false
% 51.67/7.03  --clausify_out                          false
% 51.67/7.03  --sig_cnt_out                           false
% 51.67/7.03  --trig_cnt_out                          false
% 51.67/7.03  --trig_cnt_out_tolerance                1.
% 51.67/7.03  --trig_cnt_out_sk_spl                   false
% 51.67/7.03  --abstr_cl_out                          false
% 51.67/7.03  
% 51.67/7.03  ------ Global Options
% 51.67/7.03  
% 51.67/7.03  --schedule                              default
% 51.67/7.03  --add_important_lit                     false
% 51.67/7.03  --prop_solver_per_cl                    1000
% 51.67/7.03  --min_unsat_core                        false
% 51.67/7.03  --soft_assumptions                      false
% 51.67/7.03  --soft_lemma_size                       3
% 51.67/7.03  --prop_impl_unit_size                   0
% 51.67/7.03  --prop_impl_unit                        []
% 51.67/7.03  --share_sel_clauses                     true
% 51.67/7.03  --reset_solvers                         false
% 51.67/7.03  --bc_imp_inh                            [conj_cone]
% 51.67/7.03  --conj_cone_tolerance                   3.
% 51.67/7.03  --extra_neg_conj                        none
% 51.67/7.03  --large_theory_mode                     true
% 51.67/7.03  --prolific_symb_bound                   200
% 51.67/7.03  --lt_threshold                          2000
% 51.67/7.03  --clause_weak_htbl                      true
% 51.67/7.03  --gc_record_bc_elim                     false
% 51.67/7.03  
% 51.67/7.03  ------ Preprocessing Options
% 51.67/7.03  
% 51.67/7.03  --preprocessing_flag                    true
% 51.67/7.03  --time_out_prep_mult                    0.1
% 51.67/7.03  --splitting_mode                        input
% 51.67/7.03  --splitting_grd                         true
% 51.67/7.03  --splitting_cvd                         false
% 51.67/7.03  --splitting_cvd_svl                     false
% 51.67/7.03  --splitting_nvd                         32
% 51.67/7.03  --sub_typing                            true
% 51.67/7.03  --prep_gs_sim                           true
% 51.67/7.03  --prep_unflatten                        true
% 51.67/7.03  --prep_res_sim                          true
% 51.67/7.03  --prep_upred                            true
% 51.67/7.03  --prep_sem_filter                       exhaustive
% 51.67/7.03  --prep_sem_filter_out                   false
% 51.67/7.03  --pred_elim                             true
% 51.67/7.03  --res_sim_input                         true
% 51.67/7.03  --eq_ax_congr_red                       true
% 51.67/7.03  --pure_diseq_elim                       true
% 51.67/7.03  --brand_transform                       false
% 51.67/7.03  --non_eq_to_eq                          false
% 51.67/7.03  --prep_def_merge                        true
% 51.67/7.03  --prep_def_merge_prop_impl              false
% 51.67/7.03  --prep_def_merge_mbd                    true
% 51.67/7.03  --prep_def_merge_tr_red                 false
% 51.67/7.03  --prep_def_merge_tr_cl                  false
% 51.67/7.03  --smt_preprocessing                     true
% 51.67/7.03  --smt_ac_axioms                         fast
% 51.67/7.03  --preprocessed_out                      false
% 51.67/7.03  --preprocessed_stats                    false
% 51.67/7.03  
% 51.67/7.03  ------ Abstraction refinement Options
% 51.67/7.03  
% 51.67/7.03  --abstr_ref                             []
% 51.67/7.03  --abstr_ref_prep                        false
% 51.67/7.03  --abstr_ref_until_sat                   false
% 51.67/7.03  --abstr_ref_sig_restrict                funpre
% 51.67/7.03  --abstr_ref_af_restrict_to_split_sk     false
% 51.67/7.03  --abstr_ref_under                       []
% 51.67/7.03  
% 51.67/7.03  ------ SAT Options
% 51.67/7.03  
% 51.67/7.03  --sat_mode                              false
% 51.67/7.03  --sat_fm_restart_options                ""
% 51.67/7.03  --sat_gr_def                            false
% 51.67/7.03  --sat_epr_types                         true
% 51.67/7.03  --sat_non_cyclic_types                  false
% 51.67/7.03  --sat_finite_models                     false
% 51.67/7.03  --sat_fm_lemmas                         false
% 51.67/7.03  --sat_fm_prep                           false
% 51.67/7.03  --sat_fm_uc_incr                        true
% 51.67/7.03  --sat_out_model                         small
% 51.67/7.03  --sat_out_clauses                       false
% 51.67/7.03  
% 51.67/7.03  ------ QBF Options
% 51.67/7.03  
% 51.67/7.03  --qbf_mode                              false
% 51.67/7.03  --qbf_elim_univ                         false
% 51.67/7.03  --qbf_dom_inst                          none
% 51.67/7.03  --qbf_dom_pre_inst                      false
% 51.67/7.03  --qbf_sk_in                             false
% 51.67/7.03  --qbf_pred_elim                         true
% 51.67/7.03  --qbf_split                             512
% 51.67/7.03  
% 51.67/7.03  ------ BMC1 Options
% 51.67/7.03  
% 51.67/7.03  --bmc1_incremental                      false
% 51.67/7.03  --bmc1_axioms                           reachable_all
% 51.67/7.03  --bmc1_min_bound                        0
% 51.67/7.03  --bmc1_max_bound                        -1
% 51.67/7.03  --bmc1_max_bound_default                -1
% 51.67/7.03  --bmc1_symbol_reachability              true
% 51.67/7.03  --bmc1_property_lemmas                  false
% 51.67/7.03  --bmc1_k_induction                      false
% 51.67/7.03  --bmc1_non_equiv_states                 false
% 51.67/7.03  --bmc1_deadlock                         false
% 51.67/7.03  --bmc1_ucm                              false
% 51.67/7.03  --bmc1_add_unsat_core                   none
% 51.67/7.03  --bmc1_unsat_core_children              false
% 51.67/7.03  --bmc1_unsat_core_extrapolate_axioms    false
% 51.67/7.03  --bmc1_out_stat                         full
% 51.67/7.03  --bmc1_ground_init                      false
% 51.67/7.03  --bmc1_pre_inst_next_state              false
% 51.67/7.03  --bmc1_pre_inst_state                   false
% 51.67/7.03  --bmc1_pre_inst_reach_state             false
% 51.67/7.03  --bmc1_out_unsat_core                   false
% 51.67/7.03  --bmc1_aig_witness_out                  false
% 51.67/7.03  --bmc1_verbose                          false
% 51.67/7.03  --bmc1_dump_clauses_tptp                false
% 51.67/7.03  --bmc1_dump_unsat_core_tptp             false
% 51.67/7.03  --bmc1_dump_file                        -
% 51.67/7.03  --bmc1_ucm_expand_uc_limit              128
% 51.67/7.03  --bmc1_ucm_n_expand_iterations          6
% 51.67/7.03  --bmc1_ucm_extend_mode                  1
% 51.67/7.03  --bmc1_ucm_init_mode                    2
% 51.67/7.03  --bmc1_ucm_cone_mode                    none
% 51.67/7.03  --bmc1_ucm_reduced_relation_type        0
% 51.67/7.03  --bmc1_ucm_relax_model                  4
% 51.67/7.03  --bmc1_ucm_full_tr_after_sat            true
% 51.67/7.03  --bmc1_ucm_expand_neg_assumptions       false
% 51.67/7.03  --bmc1_ucm_layered_model                none
% 51.67/7.03  --bmc1_ucm_max_lemma_size               10
% 51.67/7.03  
% 51.67/7.03  ------ AIG Options
% 51.67/7.03  
% 51.67/7.03  --aig_mode                              false
% 51.67/7.03  
% 51.67/7.03  ------ Instantiation Options
% 51.67/7.03  
% 51.67/7.03  --instantiation_flag                    true
% 51.67/7.03  --inst_sos_flag                         false
% 51.67/7.03  --inst_sos_phase                        true
% 51.67/7.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.67/7.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.67/7.03  --inst_lit_sel_side                     none
% 51.67/7.03  --inst_solver_per_active                1400
% 51.67/7.03  --inst_solver_calls_frac                1.
% 51.67/7.03  --inst_passive_queue_type               priority_queues
% 51.67/7.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.67/7.03  --inst_passive_queues_freq              [25;2]
% 51.67/7.03  --inst_dismatching                      true
% 51.67/7.03  --inst_eager_unprocessed_to_passive     true
% 51.67/7.03  --inst_prop_sim_given                   true
% 51.67/7.03  --inst_prop_sim_new                     false
% 51.67/7.03  --inst_subs_new                         false
% 51.67/7.03  --inst_eq_res_simp                      false
% 51.67/7.03  --inst_subs_given                       false
% 51.67/7.03  --inst_orphan_elimination               true
% 51.67/7.03  --inst_learning_loop_flag               true
% 51.67/7.03  --inst_learning_start                   3000
% 51.67/7.03  --inst_learning_factor                  2
% 51.67/7.03  --inst_start_prop_sim_after_learn       3
% 51.67/7.03  --inst_sel_renew                        solver
% 51.67/7.03  --inst_lit_activity_flag                true
% 51.67/7.03  --inst_restr_to_given                   false
% 51.67/7.03  --inst_activity_threshold               500
% 51.67/7.03  --inst_out_proof                        true
% 51.67/7.03  
% 51.67/7.03  ------ Resolution Options
% 51.67/7.03  
% 51.67/7.03  --resolution_flag                       false
% 51.67/7.03  --res_lit_sel                           adaptive
% 51.67/7.03  --res_lit_sel_side                      none
% 51.67/7.03  --res_ordering                          kbo
% 51.67/7.03  --res_to_prop_solver                    active
% 51.67/7.03  --res_prop_simpl_new                    false
% 51.67/7.03  --res_prop_simpl_given                  true
% 51.67/7.03  --res_passive_queue_type                priority_queues
% 51.67/7.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.67/7.03  --res_passive_queues_freq               [15;5]
% 51.67/7.03  --res_forward_subs                      full
% 51.67/7.03  --res_backward_subs                     full
% 51.67/7.03  --res_forward_subs_resolution           true
% 51.67/7.03  --res_backward_subs_resolution          true
% 51.67/7.03  --res_orphan_elimination                true
% 51.67/7.03  --res_time_limit                        2.
% 51.67/7.03  --res_out_proof                         true
% 51.67/7.03  
% 51.67/7.03  ------ Superposition Options
% 51.67/7.03  
% 51.67/7.03  --superposition_flag                    true
% 51.67/7.03  --sup_passive_queue_type                priority_queues
% 51.67/7.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.67/7.03  --sup_passive_queues_freq               [8;1;4]
% 51.67/7.03  --demod_completeness_check              fast
% 51.67/7.03  --demod_use_ground                      true
% 51.67/7.03  --sup_to_prop_solver                    passive
% 51.67/7.03  --sup_prop_simpl_new                    true
% 51.67/7.03  --sup_prop_simpl_given                  true
% 51.67/7.03  --sup_fun_splitting                     false
% 51.67/7.03  --sup_smt_interval                      50000
% 51.67/7.03  
% 51.67/7.03  ------ Superposition Simplification Setup
% 51.67/7.03  
% 51.67/7.03  --sup_indices_passive                   []
% 51.67/7.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.67/7.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.67/7.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.67/7.03  --sup_full_triv                         [TrivRules;PropSubs]
% 51.67/7.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.67/7.03  --sup_full_bw                           [BwDemod]
% 51.67/7.03  --sup_immed_triv                        [TrivRules]
% 51.67/7.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.67/7.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.67/7.03  --sup_immed_bw_main                     []
% 51.67/7.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.67/7.03  --sup_input_triv                        [Unflattening;TrivRules]
% 51.67/7.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.67/7.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.67/7.03  
% 51.67/7.03  ------ Combination Options
% 51.67/7.03  
% 51.67/7.03  --comb_res_mult                         3
% 51.67/7.03  --comb_sup_mult                         2
% 51.67/7.03  --comb_inst_mult                        10
% 51.67/7.03  
% 51.67/7.03  ------ Debug Options
% 51.67/7.03  
% 51.67/7.03  --dbg_backtrace                         false
% 51.67/7.03  --dbg_dump_prop_clauses                 false
% 51.67/7.03  --dbg_dump_prop_clauses_file            -
% 51.67/7.03  --dbg_out_stat                          false
% 51.67/7.03  
% 51.67/7.03  
% 51.67/7.03  
% 51.67/7.03  
% 51.67/7.03  ------ Proving...
% 51.67/7.03  
% 51.67/7.03  
% 51.67/7.03  % SZS status Theorem for theBenchmark.p
% 51.67/7.03  
% 51.67/7.03  % SZS output start CNFRefutation for theBenchmark.p
% 51.67/7.03  
% 51.67/7.03  fof(f14,conjecture,(
% 51.67/7.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 51.67/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.67/7.03  
% 51.67/7.03  fof(f15,negated_conjecture,(
% 51.67/7.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 51.67/7.03    inference(negated_conjecture,[],[f14])).
% 51.67/7.03  
% 51.67/7.03  fof(f39,plain,(
% 51.67/7.03    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 51.67/7.03    inference(ennf_transformation,[],[f15])).
% 51.67/7.03  
% 51.67/7.03  fof(f40,plain,(
% 51.67/7.03    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 51.67/7.03    inference(flattening,[],[f39])).
% 51.67/7.03  
% 51.67/7.03  fof(f47,plain,(
% 51.67/7.03    ? [X0] : (? [X1] : ((((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 51.67/7.03    inference(nnf_transformation,[],[f40])).
% 51.67/7.03  
% 51.67/7.03  fof(f48,plain,(
% 51.67/7.03    ? [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 51.67/7.03    inference(flattening,[],[f47])).
% 51.67/7.03  
% 51.67/7.03  fof(f50,plain,(
% 51.67/7.03    ( ! [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~m1_subset_1(k7_tmap_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))))) | ~v5_pre_topc(k7_tmap_1(X0,sK2),X0,k6_tmap_1(X0,sK2)) | ~v1_funct_2(k7_tmap_1(X0,sK2),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))) | ~v1_funct_1(k7_tmap_1(X0,sK2)) | ~v3_pre_topc(sK2,X0)) & ((m1_subset_1(k7_tmap_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))))) & v5_pre_topc(k7_tmap_1(X0,sK2),X0,k6_tmap_1(X0,sK2)) & v1_funct_2(k7_tmap_1(X0,sK2),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))) & v1_funct_1(k7_tmap_1(X0,sK2))) | v3_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 51.67/7.03    introduced(choice_axiom,[])).
% 51.67/7.03  
% 51.67/7.03  fof(f49,plain,(
% 51.67/7.03    ? [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k7_tmap_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))))) | ~v5_pre_topc(k7_tmap_1(sK1,X1),sK1,k6_tmap_1(sK1,X1)) | ~v1_funct_2(k7_tmap_1(sK1,X1),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))) | ~v1_funct_1(k7_tmap_1(sK1,X1)) | ~v3_pre_topc(X1,sK1)) & ((m1_subset_1(k7_tmap_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))))) & v5_pre_topc(k7_tmap_1(sK1,X1),sK1,k6_tmap_1(sK1,X1)) & v1_funct_2(k7_tmap_1(sK1,X1),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))) & v1_funct_1(k7_tmap_1(sK1,X1))) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 51.67/7.03    introduced(choice_axiom,[])).
% 51.67/7.03  
% 51.67/7.03  fof(f51,plain,(
% 51.67/7.03    ((~m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) | ~v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) | ~v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) | ~v1_funct_1(k7_tmap_1(sK1,sK2)) | ~v3_pre_topc(sK2,sK1)) & ((m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) & v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) & v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) & v1_funct_1(k7_tmap_1(sK1,sK2))) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 51.67/7.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).
% 51.67/7.03  
% 51.67/7.03  fof(f81,plain,(
% 51.67/7.03    l1_pre_topc(sK1)),
% 51.67/7.03    inference(cnf_transformation,[],[f51])).
% 51.67/7.03  
% 51.67/7.03  fof(f4,axiom,(
% 51.67/7.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 51.67/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.67/7.03  
% 51.67/7.03  fof(f20,plain,(
% 51.67/7.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 51.67/7.03    inference(ennf_transformation,[],[f4])).
% 51.67/7.03  
% 51.67/7.03  fof(f55,plain,(
% 51.67/7.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f20])).
% 51.67/7.03  
% 51.67/7.03  fof(f3,axiom,(
% 51.67/7.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 51.67/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.67/7.03  
% 51.67/7.03  fof(f19,plain,(
% 51.67/7.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 51.67/7.03    inference(ennf_transformation,[],[f3])).
% 51.67/7.03  
% 51.67/7.03  fof(f54,plain,(
% 51.67/7.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f19])).
% 51.67/7.03  
% 51.67/7.03  fof(f82,plain,(
% 51.67/7.03    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 51.67/7.03    inference(cnf_transformation,[],[f51])).
% 51.67/7.03  
% 51.67/7.03  fof(f11,axiom,(
% 51.67/7.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 51.67/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.67/7.03  
% 51.67/7.03  fof(f33,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.67/7.03    inference(ennf_transformation,[],[f11])).
% 51.67/7.03  
% 51.67/7.03  fof(f34,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.67/7.03    inference(flattening,[],[f33])).
% 51.67/7.03  
% 51.67/7.03  fof(f74,plain,(
% 51.67/7.03    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f34])).
% 51.67/7.03  
% 51.67/7.03  fof(f79,plain,(
% 51.67/7.03    ~v2_struct_0(sK1)),
% 51.67/7.03    inference(cnf_transformation,[],[f51])).
% 51.67/7.03  
% 51.67/7.03  fof(f80,plain,(
% 51.67/7.03    v2_pre_topc(sK1)),
% 51.67/7.03    inference(cnf_transformation,[],[f51])).
% 51.67/7.03  
% 51.67/7.03  fof(f7,axiom,(
% 51.67/7.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_struct_0(X1) = k1_xboole_0 => k2_struct_0(X0) = k1_xboole_0) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 51.67/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.67/7.03  
% 51.67/7.03  fof(f25,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 51.67/7.03    inference(ennf_transformation,[],[f7])).
% 51.67/7.03  
% 51.67/7.03  fof(f26,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 51.67/7.03    inference(flattening,[],[f25])).
% 51.67/7.03  
% 51.67/7.03  fof(f42,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 51.67/7.03    inference(nnf_transformation,[],[f26])).
% 51.67/7.03  
% 51.67/7.03  fof(f43,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 51.67/7.03    inference(rectify,[],[f42])).
% 51.67/7.03  
% 51.67/7.03  fof(f44,plain,(
% 51.67/7.03    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v3_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 51.67/7.03    introduced(choice_axiom,[])).
% 51.67/7.03  
% 51.67/7.03  fof(f45,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v3_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 51.67/7.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 51.67/7.03  
% 51.67/7.03  fof(f60,plain,(
% 51.67/7.03    ( ! [X4,X2,X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f45])).
% 51.67/7.03  
% 51.67/7.03  fof(f9,axiom,(
% 51.67/7.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 51.67/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.67/7.03  
% 51.67/7.03  fof(f16,plain,(
% 51.67/7.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 51.67/7.03    inference(pure_predicate_removal,[],[f9])).
% 51.67/7.03  
% 51.67/7.03  fof(f29,plain,(
% 51.67/7.03    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.67/7.03    inference(ennf_transformation,[],[f16])).
% 51.67/7.03  
% 51.67/7.03  fof(f30,plain,(
% 51.67/7.03    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.67/7.03    inference(flattening,[],[f29])).
% 51.67/7.03  
% 51.67/7.03  fof(f70,plain,(
% 51.67/7.03    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f30])).
% 51.67/7.03  
% 51.67/7.03  fof(f66,plain,(
% 51.67/7.03    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f45])).
% 51.67/7.03  
% 51.67/7.03  fof(f8,axiom,(
% 51.67/7.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)))),
% 51.67/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.67/7.03  
% 51.67/7.03  fof(f27,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.67/7.03    inference(ennf_transformation,[],[f8])).
% 51.67/7.03  
% 51.67/7.03  fof(f28,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.67/7.03    inference(flattening,[],[f27])).
% 51.67/7.03  
% 51.67/7.03  fof(f68,plain,(
% 51.67/7.03    ( ! [X0,X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f28])).
% 51.67/7.03  
% 51.67/7.03  fof(f10,axiom,(
% 51.67/7.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 51.67/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.67/7.03  
% 51.67/7.03  fof(f31,plain,(
% 51.67/7.03    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.67/7.03    inference(ennf_transformation,[],[f10])).
% 51.67/7.03  
% 51.67/7.03  fof(f32,plain,(
% 51.67/7.03    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.67/7.03    inference(flattening,[],[f31])).
% 51.67/7.03  
% 51.67/7.03  fof(f73,plain,(
% 51.67/7.03    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f32])).
% 51.67/7.03  
% 51.67/7.03  fof(f64,plain,(
% 51.67/7.03    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v3_pre_topc(sK0(X0,X1,X2),X1) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f45])).
% 51.67/7.03  
% 51.67/7.03  fof(f72,plain,(
% 51.67/7.03    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f32])).
% 51.67/7.03  
% 51.67/7.03  fof(f71,plain,(
% 51.67/7.03    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f32])).
% 51.67/7.03  
% 51.67/7.03  fof(f2,axiom,(
% 51.67/7.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 51.67/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.67/7.03  
% 51.67/7.03  fof(f18,plain,(
% 51.67/7.03    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.67/7.03    inference(ennf_transformation,[],[f2])).
% 51.67/7.03  
% 51.67/7.03  fof(f53,plain,(
% 51.67/7.03    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.67/7.03    inference(cnf_transformation,[],[f18])).
% 51.67/7.03  
% 51.67/7.03  fof(f12,axiom,(
% 51.67/7.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 51.67/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.67/7.03  
% 51.67/7.03  fof(f35,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.67/7.03    inference(ennf_transformation,[],[f12])).
% 51.67/7.03  
% 51.67/7.03  fof(f36,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.67/7.03    inference(flattening,[],[f35])).
% 51.67/7.03  
% 51.67/7.03  fof(f76,plain,(
% 51.67/7.03    ( ! [X2,X0,X1] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f36])).
% 51.67/7.03  
% 51.67/7.03  fof(f90,plain,(
% 51.67/7.03    ( ! [X2,X0] : (v3_pre_topc(X2,k6_tmap_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.67/7.03    inference(equality_resolution,[],[f76])).
% 51.67/7.03  
% 51.67/7.03  fof(f83,plain,(
% 51.67/7.03    v1_funct_1(k7_tmap_1(sK1,sK2)) | v3_pre_topc(sK2,sK1)),
% 51.67/7.03    inference(cnf_transformation,[],[f51])).
% 51.67/7.03  
% 51.67/7.03  fof(f85,plain,(
% 51.67/7.03    v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) | v3_pre_topc(sK2,sK1)),
% 51.67/7.03    inference(cnf_transformation,[],[f51])).
% 51.67/7.03  
% 51.67/7.03  fof(f84,plain,(
% 51.67/7.03    v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) | v3_pre_topc(sK2,sK1)),
% 51.67/7.03    inference(cnf_transformation,[],[f51])).
% 51.67/7.03  
% 51.67/7.03  fof(f86,plain,(
% 51.67/7.03    m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) | v3_pre_topc(sK2,sK1)),
% 51.67/7.03    inference(cnf_transformation,[],[f51])).
% 51.67/7.03  
% 51.67/7.03  fof(f13,axiom,(
% 51.67/7.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 51.67/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.67/7.03  
% 51.67/7.03  fof(f37,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.67/7.03    inference(ennf_transformation,[],[f13])).
% 51.67/7.03  
% 51.67/7.03  fof(f38,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.67/7.03    inference(flattening,[],[f37])).
% 51.67/7.03  
% 51.67/7.03  fof(f46,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.67/7.03    inference(nnf_transformation,[],[f38])).
% 51.67/7.03  
% 51.67/7.03  fof(f77,plain,(
% 51.67/7.03    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f46])).
% 51.67/7.03  
% 51.67/7.03  fof(f5,axiom,(
% 51.67/7.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 51.67/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.67/7.03  
% 51.67/7.03  fof(f21,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 51.67/7.03    inference(ennf_transformation,[],[f5])).
% 51.67/7.03  
% 51.67/7.03  fof(f22,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 51.67/7.03    inference(flattening,[],[f21])).
% 51.67/7.03  
% 51.67/7.03  fof(f41,plain,(
% 51.67/7.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 51.67/7.03    inference(nnf_transformation,[],[f22])).
% 51.67/7.03  
% 51.67/7.03  fof(f57,plain,(
% 51.67/7.03    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f41])).
% 51.67/7.03  
% 51.67/7.03  fof(f88,plain,(
% 51.67/7.03    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 51.67/7.03    inference(equality_resolution,[],[f57])).
% 51.67/7.03  
% 51.67/7.03  fof(f69,plain,(
% 51.67/7.03    ( ! [X0,X1] : (v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f30])).
% 51.67/7.03  
% 51.67/7.03  fof(f87,plain,(
% 51.67/7.03    ~m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) | ~v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) | ~v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) | ~v1_funct_1(k7_tmap_1(sK1,sK2)) | ~v3_pre_topc(sK2,sK1)),
% 51.67/7.03    inference(cnf_transformation,[],[f51])).
% 51.67/7.03  
% 51.67/7.03  fof(f62,plain,(
% 51.67/7.03    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f45])).
% 51.67/7.03  
% 51.67/7.03  fof(f1,axiom,(
% 51.67/7.03    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 51.67/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.67/7.03  
% 51.67/7.03  fof(f17,plain,(
% 51.67/7.03    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.67/7.03    inference(ennf_transformation,[],[f1])).
% 51.67/7.03  
% 51.67/7.03  fof(f52,plain,(
% 51.67/7.03    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.67/7.03    inference(cnf_transformation,[],[f17])).
% 51.67/7.03  
% 51.67/7.03  fof(f65,plain,(
% 51.67/7.03    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v3_pre_topc(sK0(X0,X1,X2),X1) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f45])).
% 51.67/7.03  
% 51.67/7.03  fof(f63,plain,(
% 51.67/7.03    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f45])).
% 51.67/7.03  
% 51.67/7.03  fof(f61,plain,(
% 51.67/7.03    ( ! [X4,X2,X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f45])).
% 51.67/7.03  
% 51.67/7.03  fof(f67,plain,(
% 51.67/7.03    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 51.67/7.03    inference(cnf_transformation,[],[f45])).
% 51.67/7.03  
% 51.67/7.03  cnf(c_33,negated_conjecture,
% 51.67/7.03      ( l1_pre_topc(sK1) ),
% 51.67/7.03      inference(cnf_transformation,[],[f81]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2781,negated_conjecture,
% 51.67/7.03      ( l1_pre_topc(sK1) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_33]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3761,plain,
% 51.67/7.03      ( l1_pre_topc(sK1) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2781]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3,plain,
% 51.67/7.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 51.67/7.03      inference(cnf_transformation,[],[f55]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2800,plain,
% 51.67/7.03      ( ~ l1_pre_topc(X0_55) | l1_struct_0(X0_55) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_3]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3742,plain,
% 51.67/7.03      ( l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | l1_struct_0(X0_55) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2800]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4348,plain,
% 51.67/7.03      ( l1_struct_0(sK1) = iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_3761,c_3742]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2,plain,
% 51.67/7.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 51.67/7.03      inference(cnf_transformation,[],[f54]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2801,plain,
% 51.67/7.03      ( ~ l1_struct_0(X0_55) | u1_struct_0(X0_55) = k2_struct_0(X0_55) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_2]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3741,plain,
% 51.67/7.03      ( u1_struct_0(X0_55) = k2_struct_0(X0_55)
% 51.67/7.03      | l1_struct_0(X0_55) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2801]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4459,plain,
% 51.67/7.03      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_4348,c_3741]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_32,negated_conjecture,
% 51.67/7.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 51.67/7.03      inference(cnf_transformation,[],[f82]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2782,negated_conjecture,
% 51.67/7.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_32]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3760,plain,
% 51.67/7.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2782]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_23,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | v2_struct_0(X1)
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 51.67/7.03      inference(cnf_transformation,[],[f74]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_35,negated_conjecture,
% 51.67/7.03      ( ~ v2_struct_0(sK1) ),
% 51.67/7.03      inference(cnf_transformation,[],[f79]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_487,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 51.67/7.03      | sK1 != X1 ),
% 51.67/7.03      inference(resolution_lifted,[status(thm)],[c_23,c_35]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_488,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | ~ v2_pre_topc(sK1)
% 51.67/7.03      | ~ l1_pre_topc(sK1)
% 51.67/7.03      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 51.67/7.03      inference(unflattening,[status(thm)],[c_487]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_34,negated_conjecture,
% 51.67/7.03      ( v2_pre_topc(sK1) ),
% 51.67/7.03      inference(cnf_transformation,[],[f80]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_492,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_488,c_34,c_33]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2775,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | u1_struct_0(k6_tmap_1(sK1,X0_53)) = u1_struct_0(sK1) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_492]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3767,plain,
% 51.67/7.03      ( u1_struct_0(k6_tmap_1(sK1,X0_53)) = u1_struct_0(sK1)
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2775]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4951,plain,
% 51.67/7.03      ( u1_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_3760,c_3767]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_15,plain,
% 51.67/7.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.67/7.03      | ~ v5_pre_topc(X0,X1,X2)
% 51.67/7.03      | ~ v3_pre_topc(X3,X2)
% 51.67/7.03      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.67/7.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 51.67/7.03      | ~ v1_funct_1(X0)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X2)
% 51.67/7.03      | k2_struct_0(X2) = k1_xboole_0 ),
% 51.67/7.03      inference(cnf_transformation,[],[f60]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2788,plain,
% 51.67/7.03      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 51.67/7.03      | ~ v5_pre_topc(X0_53,X0_55,X1_55)
% 51.67/7.03      | ~ v3_pre_topc(X1_53,X1_55)
% 51.67/7.03      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,X1_53),X0_55)
% 51.67/7.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 51.67/7.03      | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X1_55)))
% 51.67/7.03      | ~ v1_funct_1(X0_53)
% 51.67/7.03      | ~ l1_pre_topc(X1_55)
% 51.67/7.03      | ~ l1_pre_topc(X0_55)
% 51.67/7.03      | k2_struct_0(X1_55) = k1_xboole_0 ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_15]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3754,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X1_55,X0_55) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,X0_55) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X0_55),X0_53,X1_53),X1_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X1_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2788]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_5649,plain,
% 51.67/7.03      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,X1_53),X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_4951,c_3754]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_5661,plain,
% 51.67/7.03      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,X1_53),X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_5649,c_4951]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_39,plain,
% 51.67/7.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_17,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | v2_struct_0(X1)
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 51.67/7.03      inference(cnf_transformation,[],[f70]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_577,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(X1,X0))
% 51.67/7.03      | sK1 != X1 ),
% 51.67/7.03      inference(resolution_lifted,[status(thm)],[c_17,c_35]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_578,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | ~ v2_pre_topc(sK1)
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,X0))
% 51.67/7.03      | ~ l1_pre_topc(sK1) ),
% 51.67/7.03      inference(unflattening,[status(thm)],[c_577]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_582,plain,
% 51.67/7.03      ( l1_pre_topc(k6_tmap_1(sK1,X0))
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_578,c_34,c_33]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_583,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,X0)) ),
% 51.67/7.03      inference(renaming,[status(thm)],[c_582]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2770,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,X0_53)) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_583]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2932,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,X0_53)) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2770]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2934,plain,
% 51.67/7.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_2932]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_12936,plain,
% 51.67/7.03      ( l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,X1_53),X0_55) = iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
% 51.67/7.03      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_5661,c_39,c_2934]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_12937,plain,
% 51.67/7.03      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,X1_53),X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(renaming,[status(thm)],[c_12936]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_12942,plain,
% 51.67/7.03      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,X1_53),X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_12937,c_4459]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6401,plain,
% 51.67/7.03      ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1) ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_4459,c_4951]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3772,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,X0_53)) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2770]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4696,plain,
% 51.67/7.03      ( l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_3760,c_3772]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4700,plain,
% 51.67/7.03      ( l1_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_4696,c_3742]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6887,plain,
% 51.67/7.03      ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(k6_tmap_1(sK1,sK2)) ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_4700,c_3741]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_8164,plain,
% 51.67/7.03      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1) ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_6401,c_6887]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_12943,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,X1_53),X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_12942,c_8164]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_12956,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(sK1) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_4459,c_12943]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_12978,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(sK1) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_12956,c_4459]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6493,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,X0_55) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(sK1) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_4459,c_3754]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6762,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,X0_55) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(sK1) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_6493,c_4459]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_38,plain,
% 51.67/7.03      ( l1_pre_topc(sK1) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_18954,plain,
% 51.67/7.03      ( l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,X0_55) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | k2_struct_0(X0_55) = k1_xboole_0 ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_6762,c_38]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_18955,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,X0_55) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(renaming,[status(thm)],[c_18954]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_18968,plain,
% 51.67/7.03      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_6401,c_18955]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_18979,plain,
% 51.67/7.03      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_18968,c_6401]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_18980,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_18979,c_8164]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_22898,plain,
% 51.67/7.03      ( v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | k2_struct_0(sK1) = k1_xboole_0 ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_12978,c_38]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_22899,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top ),
% 51.67/7.03      inference(renaming,[status(thm)],[c_22898]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_9,plain,
% 51.67/7.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.67/7.03      | v5_pre_topc(X0,X1,X2)
% 51.67/7.03      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.67/7.03      | ~ v1_funct_1(X0)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X2)
% 51.67/7.03      | k2_struct_0(X2) = k1_xboole_0 ),
% 51.67/7.03      inference(cnf_transformation,[],[f66]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2794,plain,
% 51.67/7.03      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,X1_55)
% 51.67/7.03      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,sK0(X0_55,X1_55,X0_53)),X0_55)
% 51.67/7.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 51.67/7.03      | ~ v1_funct_1(X0_53)
% 51.67/7.03      | ~ l1_pre_topc(X1_55)
% 51.67/7.03      | ~ l1_pre_topc(X0_55)
% 51.67/7.03      | k2_struct_0(X1_55) = k1_xboole_0 ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_9]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3748,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X1_55,X0_55) = iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X0_55),X0_53,sK0(X1_55,X0_55,X0_53)),X1_55) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X1_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2794]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6501,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,sK1) = iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,sK0(X0_55,sK1,X0_53)),X0_55) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(sK1) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_4459,c_3748]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6610,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,sK1) = iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,sK0(X0_55,sK1,X0_53)),X0_55) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(sK1) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_6501,c_4459]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_16109,plain,
% 51.67/7.03      ( l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,sK0(X0_55,sK1,X0_53)),X0_55) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,sK1) = iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | k2_struct_0(sK1) = k1_xboole_0 ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_6610,c_38]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_16110,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,sK1) = iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,sK0(X0_55,sK1,X0_53)),X0_55) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(renaming,[status(thm)],[c_16109]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_16121,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,sK1) = iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(sK1,sK1,X0_53)),sK1) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(sK1) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_4459,c_16110]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_16145,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,sK1) = iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(sK1,sK1,X0_53)),sK1) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(sK1) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_16121,c_4459]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_16602,plain,
% 51.67/7.03      ( v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(sK1,sK1,X0_53)),sK1) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,sK1) = iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | k2_struct_0(sK1) = k1_xboole_0 ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_16145,c_38]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_16603,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,sK1) = iProver_top
% 51.67/7.03      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(sK1,sK1,X0_53)),sK1) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top ),
% 51.67/7.03      inference(renaming,[status(thm)],[c_16602]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_22915,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,sK1) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK0(sK1,sK1,X0_53),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | m1_subset_1(sK0(sK1,sK1,X0_53),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_22899,c_16603]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_16,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | v2_struct_0(X1)
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 51.67/7.03      inference(cnf_transformation,[],[f68]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_595,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 51.67/7.03      | sK1 != X1 ),
% 51.67/7.03      inference(resolution_lifted,[status(thm)],[c_16,c_35]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_596,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | ~ v2_pre_topc(sK1)
% 51.67/7.03      | ~ l1_pre_topc(sK1)
% 51.67/7.03      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
% 51.67/7.03      inference(unflattening,[status(thm)],[c_595]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_600,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_596,c_34,c_33]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2769,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | k7_tmap_1(sK1,X0_53) = k6_partfun1(u1_struct_0(sK1)) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_600]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3773,plain,
% 51.67/7.03      ( k7_tmap_1(sK1,X0_53) = k6_partfun1(u1_struct_0(sK1))
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2769]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_5285,plain,
% 51.67/7.03      ( k7_tmap_1(sK1,sK2) = k6_partfun1(u1_struct_0(sK1)) ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_3760,c_3773]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6399,plain,
% 51.67/7.03      ( k7_tmap_1(sK1,sK2) = k6_partfun1(k2_struct_0(sK1)) ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_4459,c_5285]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_19,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 51.67/7.03      | v2_struct_0(X1)
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X1) ),
% 51.67/7.03      inference(cnf_transformation,[],[f73]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_541,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | sK1 != X1 ),
% 51.67/7.03      inference(resolution_lifted,[status(thm)],[c_19,c_35]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_542,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))))
% 51.67/7.03      | ~ v2_pre_topc(sK1)
% 51.67/7.03      | ~ l1_pre_topc(sK1) ),
% 51.67/7.03      inference(unflattening,[status(thm)],[c_541]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_546,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0))))) ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_542,c_34,c_33]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2772,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | m1_subset_1(k7_tmap_1(sK1,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))))) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_546]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3770,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 51.67/7.03      | m1_subset_1(k7_tmap_1(sK1,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))))) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2772]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6393,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | m1_subset_1(k7_tmap_1(sK1,X0_53),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))))) = iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_4459,c_3770]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_11,plain,
% 51.67/7.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.67/7.03      | v5_pre_topc(X0,X1,X2)
% 51.67/7.03      | v3_pre_topc(sK0(X1,X2,X0),X2)
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.67/7.03      | ~ v1_funct_1(X0)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X2)
% 51.67/7.03      | k2_struct_0(X2) = k1_xboole_0 ),
% 51.67/7.03      inference(cnf_transformation,[],[f64]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2792,plain,
% 51.67/7.03      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,X1_55)
% 51.67/7.03      | v3_pre_topc(sK0(X0_55,X1_55,X0_53),X1_55)
% 51.67/7.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 51.67/7.03      | ~ v1_funct_1(X0_53)
% 51.67/7.03      | ~ l1_pre_topc(X1_55)
% 51.67/7.03      | ~ l1_pre_topc(X0_55)
% 51.67/7.03      | k2_struct_0(X1_55) = k1_xboole_0 ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_11]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3750,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X1_55,X0_55) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK0(X1_55,X0_55,X0_53),X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X1_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2792]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_5008,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_4951,c_3750]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_5133,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_5008,c_4951]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_11271,plain,
% 51.67/7.03      ( l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | k2_struct_0(X0_55) = k1_xboole_0 ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_5133,c_39,c_2934]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_11272,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(renaming,[status(thm)],[c_11271]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_11277,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_11272,c_4459]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_11288,plain,
% 51.67/7.03      ( k2_struct_0(k6_tmap_1(sK1,X0_53)) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(k7_tmap_1(sK1,X0_53),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))) != iProver_top
% 51.67/7.03      | v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53)),k6_tmap_1(sK1,X0_53)) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(k7_tmap_1(sK1,X0_53)) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,X0_53)) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_6393,c_11277]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_20,plain,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 51.67/7.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 51.67/7.03      | v2_struct_0(X0)
% 51.67/7.03      | ~ v2_pre_topc(X0)
% 51.67/7.03      | ~ l1_pre_topc(X0) ),
% 51.67/7.03      inference(cnf_transformation,[],[f72]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_406,plain,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 51.67/7.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 51.67/7.03      | ~ v2_pre_topc(X0)
% 51.67/7.03      | ~ l1_pre_topc(X0)
% 51.67/7.03      | sK1 != X0 ),
% 51.67/7.03      inference(resolution_lifted,[status(thm)],[c_20,c_35]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_407,plain,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | ~ v2_pre_topc(sK1)
% 51.67/7.03      | ~ l1_pre_topc(sK1) ),
% 51.67/7.03      inference(unflattening,[status(thm)],[c_406]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_411,plain,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_407,c_34,c_33]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2779,plain,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(sK1,X0_53),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53)))
% 51.67/7.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_411]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3763,plain,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(sK1,X0_53),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2779]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6394,plain,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(sK1,X0_53),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_4459,c_3763]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6403,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,X0_53)) = iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_4459,c_3772]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_21,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | v2_struct_0(X1)
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | v1_funct_1(k7_tmap_1(X1,X0))
% 51.67/7.03      | ~ l1_pre_topc(X1) ),
% 51.67/7.03      inference(cnf_transformation,[],[f71]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_523,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | v1_funct_1(k7_tmap_1(X1,X0))
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | sK1 != X1 ),
% 51.67/7.03      inference(resolution_lifted,[status(thm)],[c_21,c_35]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_524,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | ~ v2_pre_topc(sK1)
% 51.67/7.03      | v1_funct_1(k7_tmap_1(sK1,X0))
% 51.67/7.03      | ~ l1_pre_topc(sK1) ),
% 51.67/7.03      inference(unflattening,[status(thm)],[c_523]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_528,plain,
% 51.67/7.03      ( v1_funct_1(k7_tmap_1(sK1,X0))
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_524,c_34,c_33]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_529,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | v1_funct_1(k7_tmap_1(sK1,X0)) ),
% 51.67/7.03      inference(renaming,[status(thm)],[c_528]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2773,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | v1_funct_1(k7_tmap_1(sK1,X0_53)) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_529]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3769,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(k7_tmap_1(sK1,X0_53)) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2773]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6405,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(k7_tmap_1(sK1,X0_53)) = iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_4459,c_3769]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_22469,plain,
% 51.67/7.03      ( k2_struct_0(k6_tmap_1(sK1,X0_53)) = k1_xboole_0
% 51.67/7.03      | v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53)),k6_tmap_1(sK1,X0_53)) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_11288,c_6394,c_6403,c_6405]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_22479,plain,
% 51.67/7.03      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.03      | v5_pre_topc(k7_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_6399,c_22469]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_22480,plain,
% 51.67/7.03      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.03      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_22479,c_6399]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_22481,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_22480,c_8164]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6407,plain,
% 51.67/7.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_4459,c_3760]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_1,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.67/7.03      | k8_relset_1(X1,X1,k6_partfun1(X1),X0) = X0 ),
% 51.67/7.03      inference(cnf_transformation,[],[f53]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2802,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 51.67/7.03      | k8_relset_1(X1_53,X1_53,k6_partfun1(X1_53),X0_53) = X0_53 ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_1]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3740,plain,
% 51.67/7.03      ( k8_relset_1(X0_53,X0_53,k6_partfun1(X0_53),X1_53) = X1_53
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2802]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4359,plain,
% 51.67/7.03      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK2) = sK2 ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_3760,c_3740]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6406,plain,
% 51.67/7.03      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK2) = sK2 ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_4459,c_4359]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_22913,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.03      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(sK2,sK1) = iProver_top
% 51.67/7.03      | m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_6406,c_22899]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2805,plain,( X0_53 = X0_53 ),theory(equality) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2847,plain,
% 51.67/7.03      ( sK2 = sK2 ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_2805]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_24,plain,
% 51.67/7.03      ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
% 51.67/7.03      | v2_struct_0(X1)
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X1) ),
% 51.67/7.03      inference(cnf_transformation,[],[f90]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_466,plain,
% 51.67/7.03      ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | sK1 != X1 ),
% 51.67/7.03      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_467,plain,
% 51.67/7.03      ( v3_pre_topc(X0,k6_tmap_1(sK1,X0))
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0))))
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | ~ v2_pre_topc(sK1)
% 51.67/7.03      | ~ l1_pre_topc(sK1) ),
% 51.67/7.03      inference(unflattening,[status(thm)],[c_466]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_471,plain,
% 51.67/7.03      ( v3_pre_topc(X0,k6_tmap_1(sK1,X0))
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0))))
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_467,c_34,c_33]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2776,plain,
% 51.67/7.03      ( v3_pre_topc(X0_53,k6_tmap_1(sK1,X0_53))
% 51.67/7.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_53))))
% 51.67/7.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_471]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2914,plain,
% 51.67/7.03      ( v3_pre_topc(X0_53,k6_tmap_1(sK1,X0_53)) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_53)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2776]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2916,plain,
% 51.67/7.03      ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 51.67/7.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_2914]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2918,plain,
% 51.67/7.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | u1_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_2775]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2814,plain,
% 51.67/7.03      ( k1_zfmisc_1(X0_53) = k1_zfmisc_1(X1_53) | X0_53 != X1_53 ),
% 51.67/7.03      theory(equality) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4393,plain,
% 51.67/7.03      ( k1_zfmisc_1(X0_53) = k1_zfmisc_1(u1_struct_0(sK1))
% 51.67/7.03      | X0_53 != u1_struct_0(sK1) ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_2814]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4580,plain,
% 51.67/7.03      ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_53))) = k1_zfmisc_1(u1_struct_0(sK1))
% 51.67/7.03      | u1_struct_0(k6_tmap_1(sK1,X0_53)) != u1_struct_0(sK1) ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_4393]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4581,plain,
% 51.67/7.03      ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) = k1_zfmisc_1(u1_struct_0(sK1))
% 51.67/7.03      | u1_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_4580]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2815,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0_53,X0_54)
% 51.67/7.03      | m1_subset_1(X1_53,X1_54)
% 51.67/7.03      | X1_54 != X0_54
% 51.67/7.03      | X1_53 != X0_53 ),
% 51.67/7.03      theory(equality) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4203,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,X0_54)
% 51.67/7.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | X0_54 != k1_zfmisc_1(u1_struct_0(sK1))
% 51.67/7.03      | X0_53 != sK2 ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_2815]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4392,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 51.67/7.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | k1_zfmisc_1(X1_53) != k1_zfmisc_1(u1_struct_0(sK1))
% 51.67/7.03      | X0_53 != sK2 ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_4203]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4953,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_53))))
% 51.67/7.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_53))) != k1_zfmisc_1(u1_struct_0(sK1))
% 51.67/7.03      | X0_53 != sK2 ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_4392]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4954,plain,
% 51.67/7.03      ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_53))) != k1_zfmisc_1(u1_struct_0(sK1))
% 51.67/7.03      | X1_53 != sK2
% 51.67/7.03      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_53)))) = iProver_top
% 51.67/7.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_4953]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4956,plain,
% 51.67/7.03      ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1))
% 51.67/7.03      | sK2 != sK2
% 51.67/7.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top
% 51.67/7.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_4954]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_31,negated_conjecture,
% 51.67/7.03      ( v3_pre_topc(sK2,sK1) | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 51.67/7.03      inference(cnf_transformation,[],[f83]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2783,negated_conjecture,
% 51.67/7.03      ( v3_pre_topc(sK2,sK1) | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_31]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3759,plain,
% 51.67/7.03      ( v3_pre_topc(sK2,sK1) = iProver_top
% 51.67/7.03      | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2783]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2923,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(k7_tmap_1(sK1,X0_53)) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2773]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2925,plain,
% 51.67/7.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_2923]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4188,plain,
% 51.67/7.03      ( v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_3759,c_39,c_2925]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_5369,plain,
% 51.67/7.03      ( v1_funct_1(k6_partfun1(u1_struct_0(sK1))) = iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_5285,c_4188]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6398,plain,
% 51.67/7.03      ( v1_funct_1(k6_partfun1(k2_struct_0(sK1))) = iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_4459,c_5369]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_29,negated_conjecture,
% 51.67/7.03      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 51.67/7.03      | v3_pre_topc(sK2,sK1) ),
% 51.67/7.03      inference(cnf_transformation,[],[f85]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2785,negated_conjecture,
% 51.67/7.03      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 51.67/7.03      | v3_pre_topc(sK2,sK1) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_29]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3757,plain,
% 51.67/7.03      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2785]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_5368,plain,
% 51.67/7.03      ( v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_5285,c_3757]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_7270,plain,
% 51.67/7.03      ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_5368,c_4459]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_30,negated_conjecture,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 51.67/7.03      | v3_pre_topc(sK2,sK1) ),
% 51.67/7.03      inference(cnf_transformation,[],[f84]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2784,negated_conjecture,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 51.67/7.03      | v3_pre_topc(sK2,sK1) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_30]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3758,plain,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
% 51.67/7.03      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2784]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2905,plain,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(sK1,X0_53),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2779]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2907,plain,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
% 51.67/7.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_2905]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4257,plain,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_3758,c_39,c_2907]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_5000,plain,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_4951,c_4257]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_5367,plain,
% 51.67/7.03      ( v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_5285,c_5000]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_8551,plain,
% 51.67/7.03      ( v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) = iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_5367,c_4459]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_28,negated_conjecture,
% 51.67/7.03      ( v3_pre_topc(sK2,sK1)
% 51.67/7.03      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
% 51.67/7.03      inference(cnf_transformation,[],[f86]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2786,negated_conjecture,
% 51.67/7.03      ( v3_pre_topc(sK2,sK1)
% 51.67/7.03      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_28]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3756,plain,
% 51.67/7.03      ( v3_pre_topc(sK2,sK1) = iProver_top
% 51.67/7.03      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2786]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2926,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 51.67/7.03      | m1_subset_1(k7_tmap_1(sK1,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))))) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2772]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2928,plain,
% 51.67/7.03      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top
% 51.67/7.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_2926]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4263,plain,
% 51.67/7.03      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_3756,c_39,c_2928]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4999,plain,
% 51.67/7.03      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_4951,c_4263]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_5366,plain,
% 51.67/7.03      ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_5285,c_4999]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_8614,plain,
% 51.67/7.03      ( m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_5366,c_4459]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_23131,plain,
% 51.67/7.03      ( v3_pre_topc(sK2,sK1) = iProver_top
% 51.67/7.03      | k2_struct_0(sK1) = k1_xboole_0 ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_22913,c_32,c_39,c_2847,c_2916,c_2918,c_4581,c_4956,
% 51.67/7.03                 c_6398,c_6407,c_7270,c_8551,c_8614]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_23132,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 51.67/7.03      inference(renaming,[status(thm)],[c_23131]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_26,plain,
% 51.67/7.03      ( ~ v3_pre_topc(X0,X1)
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | v2_struct_0(X1)
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0) ),
% 51.67/7.03      inference(cnf_transformation,[],[f77]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_424,plain,
% 51.67/7.03      ( ~ v3_pre_topc(X0,X1)
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0)
% 51.67/7.03      | sK1 != X1 ),
% 51.67/7.03      inference(resolution_lifted,[status(thm)],[c_26,c_35]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_425,plain,
% 51.67/7.03      ( ~ v3_pre_topc(X0,sK1)
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | ~ v2_pre_topc(sK1)
% 51.67/7.03      | ~ l1_pre_topc(sK1)
% 51.67/7.03      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
% 51.67/7.03      inference(unflattening,[status(thm)],[c_424]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_429,plain,
% 51.67/7.03      ( ~ v3_pre_topc(X0,sK1)
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_425,c_34,c_33]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2778,plain,
% 51.67/7.03      ( ~ v3_pre_topc(X0_53,sK1)
% 51.67/7.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0_53) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_429]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3764,plain,
% 51.67/7.03      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0_53)
% 51.67/7.03      | v3_pre_topc(X0_53,sK1) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2778]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6148,plain,
% 51.67/7.03      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
% 51.67/7.03      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_3760,c_3764]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6391,plain,
% 51.67/7.03      ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
% 51.67/7.03      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_4459,c_6148]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_23142,plain,
% 51.67/7.03      ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
% 51.67/7.03      | k2_struct_0(sK1) = k1_xboole_0 ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_23132,c_6391]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4,plain,
% 51.67/7.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.67/7.03      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 51.67/7.03      | v5_pre_topc(X0,X1,X2)
% 51.67/7.03      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 51.67/7.03      | ~ v2_pre_topc(X2)
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | ~ v1_funct_1(X0)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X2) ),
% 51.67/7.03      inference(cnf_transformation,[],[f88]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2799,plain,
% 51.67/7.03      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 51.67/7.03      | ~ v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55))),u1_struct_0(X1_55))
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,X1_55)
% 51.67/7.03      | ~ v5_pre_topc(X0_53,g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)),X1_55)
% 51.67/7.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 51.67/7.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55))),u1_struct_0(X1_55))))
% 51.67/7.03      | ~ v2_pre_topc(X1_55)
% 51.67/7.03      | ~ v2_pre_topc(X0_55)
% 51.67/7.03      | ~ v1_funct_1(X0_53)
% 51.67/7.03      | ~ l1_pre_topc(X1_55)
% 51.67/7.03      | ~ l1_pre_topc(X0_55) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_4]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3743,plain,
% 51.67/7.03      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55))),u1_struct_0(X1_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,X1_55) = iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)),X1_55) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55))),u1_struct_0(X1_55)))) != iProver_top
% 51.67/7.03      | v2_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | v2_pre_topc(X1_55) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(X1_55) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2799]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6505,plain,
% 51.67/7.03      ( v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v2_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | v2_pre_topc(sK1) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(sK1) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_4459,c_3743]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6533,plain,
% 51.67/7.03      ( v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v2_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | v2_pre_topc(sK1) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(sK1) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_6505,c_4459]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_37,plain,
% 51.67/7.03      ( v2_pre_topc(sK1) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_13941,plain,
% 51.67/7.03      ( l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v2_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_6533,c_37,c_38]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_13942,plain,
% 51.67/7.03      ( v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v2_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(renaming,[status(thm)],[c_13941]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_23172,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v2_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_23142,c_13942]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_23226,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v2_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_23172,c_6401]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_24639,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v2_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_23142,c_23226]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_24671,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_55) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v2_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_24639,c_6401]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_24966,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(k7_tmap_1(sK1,X0_53),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))) != iProver_top
% 51.67/7.03      | v5_pre_topc(k7_tmap_1(sK1,X0_53),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,X0_53)) != iProver_top
% 51.67/7.03      | v5_pre_topc(k7_tmap_1(sK1,X0_53),sK1,k6_tmap_1(sK1,X0_53)) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v2_pre_topc(k6_tmap_1(sK1,X0_53)) != iProver_top
% 51.67/7.03      | v1_funct_1(k7_tmap_1(sK1,X0_53)) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,X0_53)) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_6393,c_24671]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_18,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | v2_struct_0(X1)
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | v2_pre_topc(k6_tmap_1(X1,X0))
% 51.67/7.03      | ~ l1_pre_topc(X1) ),
% 51.67/7.03      inference(cnf_transformation,[],[f69]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_559,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.67/7.03      | ~ v2_pre_topc(X1)
% 51.67/7.03      | v2_pre_topc(k6_tmap_1(X1,X0))
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | sK1 != X1 ),
% 51.67/7.03      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_560,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | v2_pre_topc(k6_tmap_1(sK1,X0))
% 51.67/7.03      | ~ v2_pre_topc(sK1)
% 51.67/7.03      | ~ l1_pre_topc(sK1) ),
% 51.67/7.03      inference(unflattening,[status(thm)],[c_559]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_564,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | v2_pre_topc(k6_tmap_1(sK1,X0)) ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_560,c_34,c_33]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2771,plain,
% 51.67/7.03      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | v2_pre_topc(k6_tmap_1(sK1,X0_53)) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_564]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3771,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v2_pre_topc(k6_tmap_1(sK1,X0_53)) = iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2771]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6404,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v2_pre_topc(k6_tmap_1(sK1,X0_53)) = iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_4459,c_3771]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_27474,plain,
% 51.67/7.03      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.03      | v5_pre_topc(k7_tmap_1(sK1,X0_53),sK1,k6_tmap_1(sK1,X0_53)) = iProver_top
% 51.67/7.03      | v5_pre_topc(k7_tmap_1(sK1,X0_53),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,X0_53)) != iProver_top
% 51.67/7.03      | k2_struct_0(sK1) = k1_xboole_0 ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_24966,c_6394,c_6403,c_6404,c_6405]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_27475,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v5_pre_topc(k7_tmap_1(sK1,X0_53),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,X0_53)) != iProver_top
% 51.67/7.03      | v5_pre_topc(k7_tmap_1(sK1,X0_53),sK1,k6_tmap_1(sK1,X0_53)) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(renaming,[status(thm)],[c_27474]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_27485,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.03      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_6399,c_27475]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_27499,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_27485,c_6399]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_27,negated_conjecture,
% 51.67/7.03      ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 51.67/7.03      | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 51.67/7.03      | ~ v3_pre_topc(sK2,sK1)
% 51.67/7.03      | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
% 51.67/7.03      | ~ v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 51.67/7.03      inference(cnf_transformation,[],[f87]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2787,negated_conjecture,
% 51.67/7.03      ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 51.67/7.03      | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 51.67/7.03      | ~ v3_pre_topc(sK2,sK1)
% 51.67/7.03      | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
% 51.67/7.03      | ~ v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_27]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3755,plain,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 51.67/7.03      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(sK2,sK1) != iProver_top
% 51.67/7.03      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 51.67/7.03      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2787]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2906,plain,
% 51.67/7.03      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 51.67/7.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_2779]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2924,plain,
% 51.67/7.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 51.67/7.03      | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_2773]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2927,plain,
% 51.67/7.03      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
% 51.67/7.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 51.67/7.03      inference(instantiation,[status(thm)],[c_2772]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3004,negated_conjecture,
% 51.67/7.03      ( ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 51.67/7.03      | ~ v3_pre_topc(sK2,sK1) ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_2787,c_32,c_27,c_2906,c_2924,c_2927]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3006,plain,
% 51.67/7.03      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_3004]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_4164,plain,
% 51.67/7.03      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_3755,c_3006]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_5370,plain,
% 51.67/7.03      ( v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_5285,c_4164]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_6395,plain,
% 51.67/7.03      ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.03      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 51.67/7.03      inference(demodulation,[status(thm)],[c_4459,c_5370]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_27509,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_27499,c_2844,c_2847,c_2849,c_6395,c_6407,c_23289]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_27516,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_23142,c_27509]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_48688,plain,
% 51.67/7.03      ( v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.03      | k2_struct_0(sK1) = k1_xboole_0 ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_22481,c_6407,c_27516]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_48689,plain,
% 51.67/7.03      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.03      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top ),
% 51.67/7.03      inference(renaming,[status(thm)],[c_48688]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_13,plain,
% 51.67/7.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.67/7.03      | v5_pre_topc(X0,X1,X2)
% 51.67/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.67/7.03      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 51.67/7.03      | ~ v1_funct_1(X0)
% 51.67/7.03      | ~ l1_pre_topc(X1)
% 51.67/7.03      | ~ l1_pre_topc(X2)
% 51.67/7.03      | k2_struct_0(X2) = k1_xboole_0 ),
% 51.67/7.03      inference(cnf_transformation,[],[f62]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_2790,plain,
% 51.67/7.03      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 51.67/7.03      | v5_pre_topc(X0_53,X0_55,X1_55)
% 51.67/7.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 51.67/7.03      | m1_subset_1(sK0(X0_55,X1_55,X0_53),k1_zfmisc_1(u1_struct_0(X1_55)))
% 51.67/7.03      | ~ v1_funct_1(X0_53)
% 51.67/7.03      | ~ l1_pre_topc(X1_55)
% 51.67/7.03      | ~ l1_pre_topc(X0_55)
% 51.67/7.03      | k2_struct_0(X1_55) = k1_xboole_0 ),
% 51.67/7.03      inference(subtyping,[status(esa)],[c_13]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_3752,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,X1_55,X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(sK0(X1_55,X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X1_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(predicate_to_equality,[status(thm)],[c_2790]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_5007,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.03      inference(superposition,[status(thm)],[c_4951,c_3752]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_5150,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.03      inference(light_normalisation,[status(thm)],[c_5007,c_4951]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_11346,plain,
% 51.67/7.03      ( l1_pre_topc(X0_55) != iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | k2_struct_0(X0_55) = k1_xboole_0 ),
% 51.67/7.03      inference(global_propositional_subsumption,
% 51.67/7.03                [status(thm)],
% 51.67/7.03                [c_5150,c_39,c_2934]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_11347,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.03      inference(renaming,[status(thm)],[c_11346]) ).
% 51.67/7.03  
% 51.67/7.03  cnf(c_11352,plain,
% 51.67/7.03      ( k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.03      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.03      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.03      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 51.67/7.03      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.03      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_11347,c_4459]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_11365,plain,
% 51.67/7.04      ( k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X0_55),k6_partfun1(u1_struct_0(X0_55)),sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)) = sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)
% 51.67/7.04      | k2_struct_0(X0_55) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_11352,c_3740]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_11855,plain,
% 51.67/7.04      ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_53)),u1_struct_0(k6_tmap_1(sK1,X0_53)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_53))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53))
% 51.67/7.04      | k2_struct_0(k6_tmap_1(sK1,X0_53)) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(k7_tmap_1(sK1,X0_53),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_53))) != iProver_top
% 51.67/7.04      | v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 51.67/7.04      | v1_funct_1(k7_tmap_1(sK1,X0_53)) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,X0_53)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_6393,c_11365]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_24154,plain,
% 51.67/7.04      ( k2_struct_0(k6_tmap_1(sK1,X0_53)) = k1_xboole_0
% 51.67/7.04      | k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_53)),u1_struct_0(k6_tmap_1(sK1,X0_53)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_53))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53))
% 51.67/7.04      | v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_11855,c_6394,c_6403,c_6405]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_24155,plain,
% 51.67/7.04      ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_53)),u1_struct_0(k6_tmap_1(sK1,X0_53)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_53))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53),k7_tmap_1(sK1,X0_53))
% 51.67/7.04      | k2_struct_0(k6_tmap_1(sK1,X0_53)) = k1_xboole_0
% 51.67/7.04      | v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.04      inference(renaming,[status(thm)],[c_24154]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_24164,plain,
% 51.67/7.04      ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(sK1,sK2)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,sK2))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))
% 51.67/7.04      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.04      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_6399,c_24155]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_24165,plain,
% 51.67/7.04      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
% 51.67/7.04      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.04      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_24164,c_6399,c_6401]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_0,plain,
% 51.67/7.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.67/7.04      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 51.67/7.04      inference(cnf_transformation,[],[f52]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_2803,plain,
% 51.67/7.04      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 51.67/7.04      | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
% 51.67/7.04      inference(subtyping,[status(esa)],[c_0]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_3739,plain,
% 51.67/7.04      ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
% 51.67/7.04      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 51.67/7.04      inference(predicate_to_equality,[status(thm)],[c_2803]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_4343,plain,
% 51.67/7.04      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X0_53) = k10_relat_1(k7_tmap_1(sK1,sK2),X0_53) ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_4263,c_3739]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_5840,plain,
% 51.67/7.04      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),X0_53) = k10_relat_1(k6_partfun1(u1_struct_0(sK1)),X0_53) ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_4343,c_4951,c_5285]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_6396,plain,
% 51.67/7.04      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),X0_53) = k10_relat_1(k6_partfun1(k2_struct_0(sK1)),X0_53) ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_4459,c_5840]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_24166,plain,
% 51.67/7.04      ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
% 51.67/7.04      | k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_24165,c_6396,c_8164]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_5011,plain,
% 51.67/7.04      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_4951,c_3752]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_5078,plain,
% 51.67/7.04      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_5011,c_4951]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_10342,plain,
% 51.67/7.04      ( l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
% 51.67/7.04      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_5078,c_39,c_2934]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_10343,plain,
% 51.67/7.04      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(renaming,[status(thm)],[c_10342]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_10348,plain,
% 51.67/7.04      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_10343,c_4459]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_10359,plain,
% 51.67/7.04      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)) = sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)
% 51.67/7.04      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_10348,c_3740]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_10771,plain,
% 51.67/7.04      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)) = sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)
% 51.67/7.04      | k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_8164,c_10359]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_21161,plain,
% 51.67/7.04      ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)) = sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)
% 51.67/7.04      | k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_10771,c_6396]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_21173,plain,
% 51.67/7.04      ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)
% 51.67/7.04      | k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_6401,c_21161]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_21181,plain,
% 51.67/7.04      ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)
% 51.67/7.04      | k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_21173,c_6401]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_22038,plain,
% 51.67/7.04      ( v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53) ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_21181,c_39,c_2934]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_22039,plain,
% 51.67/7.04      ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)
% 51.67/7.04      | k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top ),
% 51.67/7.04      inference(renaming,[status(thm)],[c_22038]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_22050,plain,
% 51.67/7.04      ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
% 51.67/7.04      | k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_8614,c_22039]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_51518,plain,
% 51.67/7.04      ( k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
% 51.67/7.04      | k2_struct_0(sK1) = k1_xboole_0 ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_24166,c_6398,c_8551,c_22050,c_27516]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_5504,plain,
% 51.67/7.04      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)),X0_55) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_4951,c_3748]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_5513,plain,
% 51.67/7.04      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)),X0_55) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_5504,c_4951]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_11551,plain,
% 51.67/7.04      ( l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)),X0_55) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
% 51.67/7.04      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_5513,c_39,c_2934]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_11552,plain,
% 51.67/7.04      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),X0_53,sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)),X0_55) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(renaming,[status(thm)],[c_11551]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_11557,plain,
% 51.67/7.04      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)),X0_55) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_11552,c_4459]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_11558,plain,
% 51.67/7.04      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),k2_struct_0(sK1),X0_53,sK0(X0_55,k6_tmap_1(sK1,sK2),X0_53)),X0_55) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_11557,c_8164]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_11570,plain,
% 51.67/7.04      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_6401,c_11558]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_11578,plain,
% 51.67/7.04      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_11570,c_6401]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_22023,plain,
% 51.67/7.04      ( v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | k2_struct_0(sK1) = k1_xboole_0 ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_11578,c_39,c_2934]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_22024,plain,
% 51.67/7.04      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top ),
% 51.67/7.04      inference(renaming,[status(thm)],[c_22023]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_22035,plain,
% 51.67/7.04      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 51.67/7.04      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 51.67/7.04      | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_6396,c_22024]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67163,plain,
% 51.67/7.04      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_22035,c_6398,c_8551,c_8614,c_27516]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67169,plain,
% 51.67/7.04      ( k2_struct_0(sK1) = k1_xboole_0
% 51.67/7.04      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_51518,c_67163]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67326,plain,
% 51.67/7.04      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_22915,c_48689,c_67169]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_10,plain,
% 51.67/7.04      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.67/7.04      | v5_pre_topc(X0,X1,X2)
% 51.67/7.04      | v3_pre_topc(sK0(X1,X2,X0),X2)
% 51.67/7.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.67/7.04      | ~ v1_funct_1(X0)
% 51.67/7.04      | ~ l1_pre_topc(X1)
% 51.67/7.04      | ~ l1_pre_topc(X2)
% 51.67/7.04      | k2_struct_0(X1) != k1_xboole_0 ),
% 51.67/7.04      inference(cnf_transformation,[],[f65]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_2793,plain,
% 51.67/7.04      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,X1_55)
% 51.67/7.04      | v3_pre_topc(sK0(X0_55,X1_55,X0_53),X1_55)
% 51.67/7.04      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 51.67/7.04      | ~ v1_funct_1(X0_53)
% 51.67/7.04      | ~ l1_pre_topc(X1_55)
% 51.67/7.04      | ~ l1_pre_topc(X0_55)
% 51.67/7.04      | k2_struct_0(X0_55) != k1_xboole_0 ),
% 51.67/7.04      inference(subtyping,[status(esa)],[c_10]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_3749,plain,
% 51.67/7.04      ( k2_struct_0(X0_55) != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,X1_55) = iProver_top
% 51.67/7.04      | v3_pre_topc(sK0(X0_55,X1_55,X0_53),X1_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(X1_55) != iProver_top ),
% 51.67/7.04      inference(predicate_to_equality,[status(thm)],[c_2793]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_10850,plain,
% 51.67/7.04      ( k2_struct_0(sK1) != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_8164,c_3749]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_10875,plain,
% 51.67/7.04      ( k2_struct_0(sK1) != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_10850,c_6401]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_18118,plain,
% 51.67/7.04      ( l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | k2_struct_0(sK1) != k1_xboole_0 ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_10875,c_39,c_2934]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_18119,plain,
% 51.67/7.04      ( k2_struct_0(sK1) != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(renaming,[status(thm)],[c_18118]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67501,plain,
% 51.67/7.04      ( k1_xboole_0 != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_18119]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_68135,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),X0_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(equality_resolution_simp,[status(thm)],[c_67501]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67562,plain,
% 51.67/7.04      ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_6401]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_12,plain,
% 51.67/7.04      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.67/7.04      | v5_pre_topc(X0,X1,X2)
% 51.67/7.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.67/7.04      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 51.67/7.04      | ~ v1_funct_1(X0)
% 51.67/7.04      | ~ l1_pre_topc(X1)
% 51.67/7.04      | ~ l1_pre_topc(X2)
% 51.67/7.04      | k2_struct_0(X1) != k1_xboole_0 ),
% 51.67/7.04      inference(cnf_transformation,[],[f63]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_2791,plain,
% 51.67/7.04      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,X1_55)
% 51.67/7.04      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 51.67/7.04      | m1_subset_1(sK0(X0_55,X1_55,X0_53),k1_zfmisc_1(u1_struct_0(X1_55)))
% 51.67/7.04      | ~ v1_funct_1(X0_53)
% 51.67/7.04      | ~ l1_pre_topc(X1_55)
% 51.67/7.04      | ~ l1_pre_topc(X0_55)
% 51.67/7.04      | k2_struct_0(X0_55) != k1_xboole_0 ),
% 51.67/7.04      inference(subtyping,[status(esa)],[c_12]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_3751,plain,
% 51.67/7.04      ( k2_struct_0(X0_55) != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,X1_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(X0_55,X1_55,X0_53),k1_zfmisc_1(u1_struct_0(X1_55))) = iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(X1_55) != iProver_top ),
% 51.67/7.04      inference(predicate_to_equality,[status(thm)],[c_2791]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_10849,plain,
% 51.67/7.04      ( k2_struct_0(sK1) != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_8164,c_3751]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_10892,plain,
% 51.67/7.04      ( k2_struct_0(sK1) != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_10849,c_6401]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_21645,plain,
% 51.67/7.04      ( l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | k2_struct_0(sK1) != k1_xboole_0 ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_10892,c_39,c_2934]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_21646,plain,
% 51.67/7.04      ( k2_struct_0(sK1) != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(renaming,[status(thm)],[c_21645]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67481,plain,
% 51.67/7.04      ( k1_xboole_0 != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_21646]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_68166,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(equality_resolution_simp,[status(thm)],[c_67481]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_90027,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_67562,c_68166]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_90061,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_90027,c_67562]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_91184,plain,
% 51.67/7.04      ( v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_90061,c_39,c_2934]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_91185,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top ),
% 51.67/7.04      inference(renaming,[status(thm)],[c_91184]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_91195,plain,
% 51.67/7.04      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)
% 51.67/7.04      | v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_91185,c_3740]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67531,plain,
% 51.67/7.04      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X0_53) = k10_relat_1(k6_partfun1(k1_xboole_0),X0_53) ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_6396]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_91358,plain,
% 51.67/7.04      ( k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)
% 51.67/7.04      | v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_91195,c_67531]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67563,plain,
% 51.67/7.04      ( k7_tmap_1(sK1,sK2) = k6_partfun1(k1_xboole_0) ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_6399]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67548,plain,
% 51.67/7.04      ( m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 51.67/7.04      | m1_subset_1(k7_tmap_1(sK1,X0_53),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,X0_53))))) = iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_6393]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67518,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)),X0_55) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v2_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_13942]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67560,plain,
% 51.67/7.04      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2) = sK2 ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_6406]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_14,plain,
% 51.67/7.04      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.67/7.04      | ~ v5_pre_topc(X0,X1,X2)
% 51.67/7.04      | ~ v3_pre_topc(X3,X2)
% 51.67/7.04      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 51.67/7.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.67/7.04      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 51.67/7.04      | ~ v1_funct_1(X0)
% 51.67/7.04      | ~ l1_pre_topc(X1)
% 51.67/7.04      | ~ l1_pre_topc(X2)
% 51.67/7.04      | k2_struct_0(X1) != k1_xboole_0 ),
% 51.67/7.04      inference(cnf_transformation,[],[f61]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_2789,plain,
% 51.67/7.04      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 51.67/7.04      | ~ v5_pre_topc(X0_53,X0_55,X1_55)
% 51.67/7.04      | ~ v3_pre_topc(X1_53,X1_55)
% 51.67/7.04      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,X1_53),X0_55)
% 51.67/7.04      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 51.67/7.04      | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X1_55)))
% 51.67/7.04      | ~ v1_funct_1(X0_53)
% 51.67/7.04      | ~ l1_pre_topc(X1_55)
% 51.67/7.04      | ~ l1_pre_topc(X0_55)
% 51.67/7.04      | k2_struct_0(X0_55) != k1_xboole_0 ),
% 51.67/7.04      inference(subtyping,[status(esa)],[c_14]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_3753,plain,
% 51.67/7.04      ( k2_struct_0(X0_55) != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,X1_55) != iProver_top
% 51.67/7.04      | v3_pre_topc(X1_53,X1_55) != iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,X1_53),X0_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 51.67/7.04      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X1_55))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(X1_55) != iProver_top ),
% 51.67/7.04      inference(predicate_to_equality,[status(thm)],[c_2789]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_68327,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
% 51.67/7.04      | v3_pre_topc(X1_53,X0_55) != iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(sK1) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_67326,c_3753]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_70702,plain,
% 51.67/7.04      ( l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.04      | v3_pre_topc(X1_53,X0_55) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_68327,c_38]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_70703,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,u1_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
% 51.67/7.04      | v3_pre_topc(X1_53,X0_55) != iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(renaming,[status(thm)],[c_70702]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67571,plain,
% 51.67/7.04      ( u1_struct_0(sK1) = k1_xboole_0 ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_4459]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_70706,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,sK1,X0_55) != iProver_top
% 51.67/7.04      | v3_pre_topc(X1_53,X0_55) != iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_55),X0_53,X1_53),sK1) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_70703,c_67571]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_70719,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,X1_53),sK1) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 51.67/7.04      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_67562,c_70706]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_70729,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,X1_53),sK1) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | m1_subset_1(X1_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_70719,c_67562]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_73465,plain,
% 51.67/7.04      ( v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | m1_subset_1(X1_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,X1_53),sK1) = iProver_top
% 51.67/7.04      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_70729,c_39,c_2934]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_73466,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v3_pre_topc(X1_53,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,X1_53),sK1) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | m1_subset_1(X1_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top ),
% 51.67/7.04      inference(renaming,[status(thm)],[c_73465]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_73479,plain,
% 51.67/7.04      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 51.67/7.04      | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v3_pre_topc(sK2,sK1) = iProver_top
% 51.67/7.04      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 51.67/7.04      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_67560,c_73466]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67559,plain,
% 51.67/7.04      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_8614]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67561,plain,
% 51.67/7.04      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_8551]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67567,plain,
% 51.67/7.04      ( v1_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_6398]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67568,plain,
% 51.67/7.04      ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_7270]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67570,plain,
% 51.67/7.04      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_6407]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_73624,plain,
% 51.67/7.04      ( v3_pre_topc(sK2,sK1) = iProver_top ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_73479,c_32,c_39,c_2847,c_2916,c_2918,c_4581,c_4956,
% 51.67/7.04                 c_67559,c_67561,c_67567,c_67568,c_67570]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67554,plain,
% 51.67/7.04      ( g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
% 51.67/7.04      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_6391]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_73629,plain,
% 51.67/7.04      ( g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2) ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_73624,c_67554]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_74842,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,sK1,X0_55) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v2_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_67518,c_67562,c_73629]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_74853,plain,
% 51.67/7.04      ( v1_funct_2(k7_tmap_1(sK1,X0_53),k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,X0_53))) != iProver_top
% 51.67/7.04      | v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) != iProver_top
% 51.67/7.04      | v5_pre_topc(k7_tmap_1(sK1,X0_53),sK1,k6_tmap_1(sK1,X0_53)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 51.67/7.04      | v2_pre_topc(k6_tmap_1(sK1,X0_53)) != iProver_top
% 51.67/7.04      | v1_funct_1(k7_tmap_1(sK1,X0_53)) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,X0_53)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_67548,c_74842]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67549,plain,
% 51.67/7.04      ( v1_funct_2(k7_tmap_1(sK1,X0_53),k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,X0_53))) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_6394]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67556,plain,
% 51.67/7.04      ( m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 51.67/7.04      | v1_funct_1(k7_tmap_1(sK1,X0_53)) = iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_6405]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67557,plain,
% 51.67/7.04      ( m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 51.67/7.04      | v2_pre_topc(k6_tmap_1(sK1,X0_53)) = iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_6404]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67558,plain,
% 51.67/7.04      ( m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,X0_53)) = iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_6403]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_74959,plain,
% 51.67/7.04      ( m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 51.67/7.04      | v5_pre_topc(k7_tmap_1(sK1,X0_53),sK1,k6_tmap_1(sK1,X0_53)) = iProver_top
% 51.67/7.04      | v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) != iProver_top ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_74853,c_67549,c_67556,c_67557,c_67558]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_74960,plain,
% 51.67/7.04      ( v5_pre_topc(k7_tmap_1(sK1,X0_53),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_53)) != iProver_top
% 51.67/7.04      | v5_pre_topc(k7_tmap_1(sK1,X0_53),sK1,k6_tmap_1(sK1,X0_53)) = iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 51.67/7.04      inference(renaming,[status(thm)],[c_74959]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_74970,plain,
% 51.67/7.04      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_67563,c_74960]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_74974,plain,
% 51.67/7.04      ( v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_74970,c_67563]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67550,plain,
% 51.67/7.04      ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_6395]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_74980,plain,
% 51.67/7.04      ( v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_74974,c_32,c_39,c_2847,c_2916,c_2918,c_4581,c_4956,
% 51.67/7.04                 c_67550,c_67559,c_67561,c_67567,c_67568,c_67570,c_73479]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_93202,plain,
% 51.67/7.04      ( k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))
% 51.67/7.04      | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 51.67/7.04      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_91358,c_74980]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_95107,plain,
% 51.67/7.04      ( k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0)) ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_93202,c_67559,c_67561,c_67567]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_8,plain,
% 51.67/7.04      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.67/7.04      | v5_pre_topc(X0,X1,X2)
% 51.67/7.04      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 51.67/7.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.67/7.04      | ~ v1_funct_1(X0)
% 51.67/7.04      | ~ l1_pre_topc(X1)
% 51.67/7.04      | ~ l1_pre_topc(X2)
% 51.67/7.04      | k2_struct_0(X1) != k1_xboole_0 ),
% 51.67/7.04      inference(cnf_transformation,[],[f67]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_2795,plain,
% 51.67/7.04      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,X1_55)
% 51.67/7.04      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,sK0(X0_55,X1_55,X0_53)),X0_55)
% 51.67/7.04      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 51.67/7.04      | ~ v1_funct_1(X0_53)
% 51.67/7.04      | ~ l1_pre_topc(X1_55)
% 51.67/7.04      | ~ l1_pre_topc(X0_55)
% 51.67/7.04      | k2_struct_0(X0_55) != k1_xboole_0 ),
% 51.67/7.04      inference(subtyping,[status(esa)],[c_8]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_3747,plain,
% 51.67/7.04      ( k2_struct_0(X0_55) != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,X0_55,X1_55) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,sK0(X0_55,X1_55,X0_53)),X0_55) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(X1_55) != iProver_top ),
% 51.67/7.04      inference(predicate_to_equality,[status(thm)],[c_2795]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_10848,plain,
% 51.67/7.04      ( k2_struct_0(sK1) != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55),X0_53,sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_8164,c_3747]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_10909,plain,
% 51.67/7.04      ( k2_struct_0(sK1) != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_55),X0_53,sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_10848,c_6401]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_13481,plain,
% 51.67/7.04      ( l1_pre_topc(X0_55) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_55),X0_53,sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | k2_struct_0(sK1) != k1_xboole_0 ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_10909,c_39,c_2934]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_13482,plain,
% 51.67/7.04      ( k2_struct_0(sK1) != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,k2_struct_0(sK1),u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_55),X0_53,sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(renaming,[status(thm)],[c_13481]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67524,plain,
% 51.67/7.04      ( k1_xboole_0 != k1_xboole_0
% 51.67/7.04      | v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_55),X0_53,sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_67326,c_13482]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_67873,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(X0_55)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),X0_55) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_55),X0_53,sK0(k6_tmap_1(sK1,sK2),X0_55,X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_55)))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(X0_55) != iProver_top ),
% 51.67/7.04      inference(equality_resolution_simp,[status(thm)],[c_67524]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_85373,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_67562,c_67873]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_85394,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_85373,c_67562]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_85509,plain,
% 51.67/7.04      ( v1_funct_1(X0_53) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_85394,c_39,c_2934]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_85510,plain,
% 51.67/7.04      ( v1_funct_2(X0_53,k1_xboole_0,k1_xboole_0) != iProver_top
% 51.67/7.04      | v5_pre_topc(X0_53,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_53,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_53)),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | v1_funct_1(X0_53) != iProver_top ),
% 51.67/7.04      inference(renaming,[status(thm)],[c_85509]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_85520,plain,
% 51.67/7.04      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 51.67/7.04      | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))),k6_tmap_1(sK1,sK2)) != iProver_top
% 51.67/7.04      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_67531,c_85510]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_85523,plain,
% 51.67/7.04      ( v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))),k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(global_propositional_subsumption,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_85520,c_32,c_39,c_2847,c_2916,c_2918,c_4581,c_4956,
% 51.67/7.04                 c_67550,c_67559,c_67561,c_67567,c_67568,c_67570,c_73479,
% 51.67/7.04                 c_74974]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_95110,plain,
% 51.67/7.04      ( v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(demodulation,[status(thm)],[c_95107,c_85523]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_158357,plain,
% 51.67/7.04      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 51.67/7.04      | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 51.67/7.04      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(superposition,[status(thm)],[c_68135,c_95110]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(c_158358,plain,
% 51.67/7.04      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 51.67/7.04      | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 51.67/7.04      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 51.67/7.04      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 51.67/7.04      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 51.67/7.04      inference(light_normalisation,[status(thm)],[c_158357,c_67562]) ).
% 51.67/7.04  
% 51.67/7.04  cnf(contradiction,plain,
% 51.67/7.04      ( $false ),
% 51.67/7.04      inference(minisat,
% 51.67/7.04                [status(thm)],
% 51.67/7.04                [c_158358,c_74974,c_73624,c_67570,c_67567,c_67561,
% 51.67/7.04                 c_67559,c_67550,c_2934,c_39]) ).
% 51.67/7.04  
% 51.67/7.04  
% 51.67/7.04  % SZS output end CNFRefutation for theBenchmark.p
% 51.67/7.04  
% 51.67/7.04  ------                               Statistics
% 51.67/7.04  
% 51.67/7.04  ------ General
% 51.67/7.04  
% 51.67/7.04  abstr_ref_over_cycles:                  0
% 51.67/7.04  abstr_ref_under_cycles:                 0
% 51.67/7.04  gc_basic_clause_elim:                   0
% 51.67/7.04  forced_gc_time:                         0
% 51.67/7.04  parsing_time:                           0.009
% 51.67/7.04  unif_index_cands_time:                  0.
% 51.67/7.04  unif_index_add_time:                    0.
% 51.67/7.04  orderings_time:                         0.
% 51.67/7.04  out_proof_time:                         0.057
% 51.67/7.04  total_time:                             6.16
% 51.67/7.04  num_of_symbols:                         60
% 51.67/7.04  num_of_terms:                           78495
% 51.67/7.04  
% 51.67/7.04  ------ Preprocessing
% 51.67/7.04  
% 51.67/7.04  num_of_splits:                          0
% 51.67/7.04  num_of_split_atoms:                     0
% 51.67/7.04  num_of_reused_defs:                     0
% 51.67/7.04  num_eq_ax_congr_red:                    25
% 51.67/7.04  num_of_sem_filtered_clauses:            1
% 51.67/7.04  num_of_subtypes:                        4
% 51.67/7.04  monotx_restored_types:                  0
% 51.67/7.04  sat_num_of_epr_types:                   0
% 51.67/7.04  sat_num_of_non_cyclic_types:            0
% 51.67/7.04  sat_guarded_non_collapsed_types:        1
% 51.67/7.04  num_pure_diseq_elim:                    0
% 51.67/7.04  simp_replaced_by:                       0
% 51.67/7.04  res_preprocessed:                       190
% 51.67/7.04  prep_upred:                             0
% 51.67/7.04  prep_unflattend:                        59
% 51.67/7.04  smt_new_axioms:                         0
% 51.67/7.04  pred_elim_cands:                        8
% 51.67/7.04  pred_elim:                              1
% 51.67/7.04  pred_elim_cl:                           1
% 51.67/7.04  pred_elim_cycles:                       3
% 51.67/7.04  merged_defs:                            4
% 51.67/7.04  merged_defs_ncl:                        0
% 51.67/7.04  bin_hyper_res:                          4
% 51.67/7.04  prep_cycles:                            4
% 51.67/7.04  pred_elim_time:                         0.06
% 51.67/7.04  splitting_time:                         0.
% 51.67/7.04  sem_filter_time:                        0.
% 51.67/7.04  monotx_time:                            0.
% 51.67/7.04  subtype_inf_time:                       0.001
% 51.67/7.04  
% 51.67/7.04  ------ Problem properties
% 51.67/7.04  
% 51.67/7.04  clauses:                                35
% 51.67/7.04  conjectures:                            8
% 51.67/7.04  epr:                                    3
% 51.67/7.04  horn:                                   24
% 51.67/7.04  ground:                                 8
% 51.67/7.04  unary:                                  3
% 51.67/7.04  binary:                                 16
% 51.67/7.04  lits:                                   153
% 51.67/7.04  lits_eq:                                20
% 51.67/7.04  fd_pure:                                0
% 51.67/7.04  fd_pseudo:                              0
% 51.67/7.04  fd_cond:                                0
% 51.67/7.04  fd_pseudo_cond:                         0
% 51.67/7.04  ac_symbols:                             0
% 51.67/7.04  
% 51.67/7.04  ------ Propositional Solver
% 51.67/7.04  
% 51.67/7.04  prop_solver_calls:                      48
% 51.67/7.04  prop_fast_solver_calls:                 19198
% 51.67/7.04  smt_solver_calls:                       0
% 51.67/7.04  smt_fast_solver_calls:                  0
% 51.67/7.04  prop_num_of_clauses:                    36846
% 51.67/7.04  prop_preprocess_simplified:             112145
% 51.67/7.04  prop_fo_subsumed:                       4240
% 51.67/7.04  prop_solver_time:                       0.
% 51.67/7.04  smt_solver_time:                        0.
% 51.67/7.04  smt_fast_solver_time:                   0.
% 51.67/7.04  prop_fast_solver_time:                  0.
% 51.67/7.04  prop_unsat_core_time:                   0.003
% 51.67/7.04  
% 51.67/7.04  ------ QBF
% 51.67/7.04  
% 51.67/7.04  qbf_q_res:                              0
% 51.67/7.04  qbf_num_tautologies:                    0
% 51.67/7.04  qbf_prep_cycles:                        0
% 51.67/7.04  
% 51.67/7.04  ------ BMC1
% 51.67/7.04  
% 51.67/7.04  bmc1_current_bound:                     -1
% 51.67/7.04  bmc1_last_solved_bound:                 -1
% 51.67/7.04  bmc1_unsat_core_size:                   -1
% 51.67/7.04  bmc1_unsat_core_parents_size:           -1
% 51.67/7.04  bmc1_merge_next_fun:                    0
% 51.67/7.04  bmc1_unsat_core_clauses_time:           0.
% 51.67/7.04  
% 51.67/7.04  ------ Instantiation
% 51.67/7.04  
% 51.67/7.04  inst_num_of_clauses:                    7408
% 51.67/7.04  inst_num_in_passive:                    3190
% 51.67/7.04  inst_num_in_active:                     5098
% 51.67/7.04  inst_num_in_unprocessed:                1609
% 51.67/7.04  inst_num_of_loops:                      6329
% 51.67/7.04  inst_num_of_learning_restarts:          1
% 51.67/7.04  inst_num_moves_active_passive:          1226
% 51.67/7.04  inst_lit_activity:                      0
% 51.67/7.04  inst_lit_activity_moves:                4
% 51.67/7.04  inst_num_tautologies:                   0
% 51.67/7.04  inst_num_prop_implied:                  0
% 51.67/7.04  inst_num_existing_simplified:           0
% 51.67/7.04  inst_num_eq_res_simplified:             0
% 51.67/7.04  inst_num_child_elim:                    0
% 51.67/7.04  inst_num_of_dismatching_blockings:      13234
% 51.67/7.04  inst_num_of_non_proper_insts:           17191
% 51.67/7.04  inst_num_of_duplicates:                 0
% 51.67/7.04  inst_inst_num_from_inst_to_res:         0
% 51.67/7.04  inst_dismatching_checking_time:         0.
% 51.67/7.04  
% 51.67/7.04  ------ Resolution
% 51.67/7.04  
% 51.67/7.04  res_num_of_clauses:                     59
% 51.67/7.04  res_num_in_passive:                     59
% 51.67/7.04  res_num_in_active:                      0
% 51.67/7.04  res_num_of_loops:                       194
% 51.67/7.04  res_forward_subset_subsumed:            907
% 51.67/7.04  res_backward_subset_subsumed:           8
% 51.67/7.04  res_forward_subsumed:                   0
% 51.67/7.04  res_backward_subsumed:                  0
% 51.67/7.04  res_forward_subsumption_resolution:     0
% 51.67/7.04  res_backward_subsumption_resolution:    0
% 51.67/7.04  res_clause_to_clause_subsumption:       11220
% 51.67/7.04  res_orphan_elimination:                 0
% 51.67/7.04  res_tautology_del:                      1158
% 51.67/7.04  res_num_eq_res_simplified:              0
% 51.67/7.04  res_num_sel_changes:                    0
% 51.67/7.04  res_moves_from_active_to_pass:          0
% 51.67/7.04  
% 51.67/7.04  ------ Superposition
% 51.67/7.04  
% 51.67/7.04  sup_time_total:                         0.
% 51.67/7.04  sup_time_generating:                    0.
% 51.67/7.04  sup_time_sim_full:                      0.
% 51.67/7.04  sup_time_sim_immed:                     0.
% 51.67/7.04  
% 51.67/7.04  sup_num_of_clauses:                     1024
% 51.67/7.04  sup_num_in_active:                      722
% 51.67/7.04  sup_num_in_passive:                     302
% 51.67/7.04  sup_num_of_loops:                       1264
% 51.67/7.04  sup_fw_superposition:                   1526
% 51.67/7.04  sup_bw_superposition:                   1612
% 51.67/7.04  sup_immediate_simplified:               1172
% 51.67/7.04  sup_given_eliminated:                   4
% 51.67/7.04  comparisons_done:                       0
% 51.67/7.04  comparisons_avoided:                    960
% 51.67/7.04  
% 51.67/7.04  ------ Simplifications
% 51.67/7.04  
% 51.67/7.04  
% 51.67/7.04  sim_fw_subset_subsumed:                 276
% 51.67/7.04  sim_bw_subset_subsumed:                 532
% 51.67/7.04  sim_fw_subsumed:                        190
% 51.67/7.04  sim_bw_subsumed:                        38
% 51.67/7.04  sim_fw_subsumption_res:                 1
% 51.67/7.04  sim_bw_subsumption_res:                 0
% 51.67/7.04  sim_tautology_del:                      156
% 51.67/7.04  sim_eq_tautology_del:                   189
% 51.67/7.04  sim_eq_res_simp:                        5
% 51.67/7.04  sim_fw_demodulated:                     124
% 51.67/7.04  sim_bw_demodulated:                     350
% 51.67/7.04  sim_light_normalised:                   876
% 51.67/7.04  sim_joinable_taut:                      0
% 51.67/7.04  sim_joinable_simp:                      0
% 51.67/7.04  sim_ac_normalised:                      0
% 51.67/7.04  sim_smt_subsumption:                    0
% 51.67/7.04  
%------------------------------------------------------------------------------
