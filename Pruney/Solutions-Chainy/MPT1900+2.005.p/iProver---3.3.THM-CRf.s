%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:51 EST 2020

% Result     : Theorem 7.45s
% Output     : CNFRefutation 7.45s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2458)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f73,plain,(
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
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f74,plain,(
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
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f73])).

fof(f75,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
        & v3_pre_topc(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
                    & v3_pre_topc(sK2(X0,X1,X2),X1)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f74,f75])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f27,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v5_pre_topc(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ v5_pre_topc(sK8,X0,X1)
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ~ v5_pre_topc(X2,X0,sK7)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK7))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK7)
        & v2_pre_topc(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v5_pre_topc(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,sK6,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK6)
      & v1_tdlat_3(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,
    ( ~ v5_pre_topc(sK8,sK6,sK7)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    & v1_funct_1(sK8)
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & l1_pre_topc(sK6)
    & v1_tdlat_3(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f57,f91,f90,f89])).

fof(f149,plain,(
    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f92])).

fof(f148,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f92])).

fof(f145,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f92])).

fof(f147,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f92])).

fof(f150,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f92])).

fof(f151,plain,(
    ~ v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f92])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f143,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f92])).

fof(f144,plain,(
    v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f92])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f81,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f82,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f81])).

fof(f83,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK4(X0),X0)
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f82,f83])).

fof(f137,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f120,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f122,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f121,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f99,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f58])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f59,f60])).

fof(f94,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f23,axiom,(
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
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f77])).

fof(f79,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2))))
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2))))
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f78,f79])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f146,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f92])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f62])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f63,f64])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f93,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f85,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f86,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f85])).

fof(f87,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK5(X0),X0)
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f86,f87])).

fof(f140,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f136,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f72,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(rectify,[],[f29])).

fof(f114,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f72])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f68])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f154,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f106])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f113,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_52,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_1322,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0
    | u1_struct_0(X2) != u1_struct_0(sK7)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_52])).

cnf(c_1323,plain,
    ( v5_pre_topc(sK8,X0,X1)
    | m1_subset_1(sK2(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK8)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) = k1_xboole_0
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1322])).

cnf(c_53,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_1327,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | m1_subset_1(sK2(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
    | v5_pre_topc(sK8,X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) = k1_xboole_0
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1323,c_53])).

cnf(c_1328,plain,
    ( v5_pre_topc(sK8,X0,X1)
    | m1_subset_1(sK2(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) = k1_xboole_0
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(renaming,[status(thm)],[c_1327])).

cnf(c_5279,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | v5_pre_topc(sK8,X1,X0) = iProver_top
    | m1_subset_1(sK2(X1,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1328])).

cnf(c_6282,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | v5_pre_topc(sK8,sK6,X0) = iProver_top
    | m1_subset_1(sK2(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5279])).

cnf(c_56,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_61,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_5792,plain,
    ( v5_pre_topc(sK8,sK6,X0)
    | m1_subset_1(sK2(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK6)
    | k2_struct_0(X0) = k1_xboole_0
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1328])).

cnf(c_5793,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | v5_pre_topc(sK8,sK6,X0) = iProver_top
    | m1_subset_1(sK2(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5792])).

cnf(c_4189,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6243,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4189])).

cnf(c_6965,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(sK2(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v5_pre_topc(sK8,sK6,X0) = iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | k2_struct_0(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6282,c_61,c_5793,c_6243])).

cnf(c_6966,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | v5_pre_topc(sK8,sK6,X0) = iProver_top
    | m1_subset_1(sK2(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6965])).

cnf(c_6977,plain,
    ( k2_struct_0(sK7) = k1_xboole_0
    | v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | m1_subset_1(sK2(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_6966])).

cnf(c_54,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_63,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_51,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_66,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_50,negated_conjecture,
    ( ~ v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_67,plain,
    ( v5_pre_topc(sK8,sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_7414,plain,
    ( k2_struct_0(sK7) = k1_xboole_0
    | m1_subset_1(sK2(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6977,c_2458,c_6243,c_6575])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_5307,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9915,plain,
    ( k2_struct_0(sK7) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK7)) = iProver_top
    | r2_hidden(X0,sK2(sK6,sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7414,c_5307])).

cnf(c_58,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_57,negated_conjecture,
    ( v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1466,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0
    | u1_struct_0(X2) != u1_struct_0(sK7)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_52])).

cnf(c_1467,plain,
    ( v5_pre_topc(sK8,X0,X1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK2(X0,X1,sK8)),X0)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK8)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) = k1_xboole_0
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1466])).

cnf(c_1471,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK2(X0,X1,sK8)),X0)
    | v5_pre_topc(sK8,X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) = k1_xboole_0
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1467,c_53])).

cnf(c_1472,plain,
    ( v5_pre_topc(sK8,X0,X1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK2(X0,X1,sK8)),X0)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) = k1_xboole_0
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(renaming,[status(thm)],[c_1471])).

cnf(c_2373,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK2(X0,X1,sK8)),X0)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) = k1_xboole_0
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | sK7 != X1
    | sK6 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_50,c_1472])).

cnf(c_2374,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),sK6)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | k2_struct_0(sK7) = k1_xboole_0
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_2373])).

cnf(c_2376,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),sK6)
    | k2_struct_0(sK7) = k1_xboole_0
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2374,c_56,c_54,c_51])).

cnf(c_6575,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_4189])).

cnf(c_46,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_5986,plain,
    ( v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tdlat_3(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_6169,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK6),X0,X1,X2),sK6)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK6),X0,X1,X2),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tdlat_3(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_5986])).

cnf(c_6734,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),sK6)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tdlat_3(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_6169])).

cnf(c_8571,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),sK6)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tdlat_3(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_6734])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_5995,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_9469,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(instantiation,[status(thm)],[c_5995])).

cnf(c_10557,plain,
    ( k2_struct_0(sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9915,c_58,c_57,c_56,c_51,c_2376,c_6243,c_6575,c_8571,c_9469])).

cnf(c_27,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_29,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_28,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_740,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_29,c_28])).

cnf(c_758,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_27,c_740])).

cnf(c_5288,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(k2_struct_0(X0)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_10563,plain,
    ( l1_pre_topc(sK7) != iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10557,c_5288])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_185,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11478,plain,
    ( v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10563,c_63,c_185])).

cnf(c_5294,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_5305,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9751,plain,
    ( v1_xboole_0(u1_struct_0(sK7)) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_5294,c_5305])).

cnf(c_11485,plain,
    ( v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_11478,c_9751])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_5314,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11579,plain,
    ( sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11485,c_5314])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_5320,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_41,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK3(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_1160,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK3(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK7)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_52])).

cnf(c_1161,plain,
    ( v5_pre_topc(sK8,X0,X1)
    | m1_subset_1(sK3(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK8)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1160])).

cnf(c_1165,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | m1_subset_1(sK3(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
    | v5_pre_topc(sK8,X0,X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1161,c_53])).

cnf(c_1166,plain,
    ( v5_pre_topc(sK8,X0,X1)
    | m1_subset_1(sK3(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(renaming,[status(thm)],[c_1165])).

cnf(c_5283,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | v5_pre_topc(sK8,X1,X0) = iProver_top
    | m1_subset_1(sK3(X1,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1166])).

cnf(c_6590,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | v5_pre_topc(sK8,sK6,X0) = iProver_top
    | m1_subset_1(sK3(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5283])).

cnf(c_59,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_5836,plain,
    ( v5_pre_topc(sK8,sK6,X0)
    | m1_subset_1(sK3(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_5837,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | v5_pre_topc(sK8,sK6,X0) = iProver_top
    | m1_subset_1(sK3(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5836])).

cnf(c_7131,plain,
    ( l1_pre_topc(X0) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | v5_pre_topc(sK8,sK6,X0) = iProver_top
    | m1_subset_1(sK3(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6590,c_59,c_61,c_5837,c_6243])).

cnf(c_7132,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | v5_pre_topc(sK8,sK6,X0) = iProver_top
    | m1_subset_1(sK3(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7131])).

cnf(c_7143,plain,
    ( v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_7132])).

cnf(c_2490,plain,
    ( m1_subset_1(sK3(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | sK7 != X1
    | sK6 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_50,c_1166])).

cnf(c_2491,plain,
    ( m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_2490])).

cnf(c_55,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_2493,plain,
    ( m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7)))
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2491,c_58,c_56,c_55,c_54,c_51])).

cnf(c_2495,plain,
    ( u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2493])).

cnf(c_7492,plain,
    ( m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7143,c_2495,c_6243,c_6575])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_5308,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7497,plain,
    ( r1_tarski(sK3(sK6,sK7,sK8),u1_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7492,c_5308])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_5316,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8027,plain,
    ( r2_hidden(X0,sK3(sK6,sK7,sK8)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7497,c_5316])).

cnf(c_8594,plain,
    ( r2_hidden(sK0(sK3(sK6,sK7,sK8)),u1_struct_0(sK7)) = iProver_top
    | v1_xboole_0(sK3(sK6,sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5320,c_8027])).

cnf(c_11600,plain,
    ( r2_hidden(sK0(sK3(sK6,sK7,k1_xboole_0)),u1_struct_0(sK7)) = iProver_top
    | v1_xboole_0(sK3(sK6,sK7,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11579,c_8594])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_5319,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18204,plain,
    ( v1_xboole_0(sK3(sK6,sK7,k1_xboole_0)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11600,c_5319])).

cnf(c_18624,plain,
    ( v1_xboole_0(sK3(sK6,sK7,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18204,c_63,c_185,c_10563])).

cnf(c_18629,plain,
    ( sK3(sK6,sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18624,c_5314])).

cnf(c_11483,plain,
    ( u1_struct_0(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11478,c_5314])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK3(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK3(X1,X2,X0))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_1199,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK3(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK3(X1,X2,X0))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK7)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_52])).

cnf(c_1200,plain,
    ( v5_pre_topc(sK8,X0,X1)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK3(X0,X1,sK8))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,k2_pre_topc(X1,sK3(X0,X1,sK8))))
    | ~ v1_funct_1(sK8)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1199])).

cnf(c_1204,plain,
    ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK3(X0,X1,sK8))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,k2_pre_topc(X1,sK3(X0,X1,sK8))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v5_pre_topc(sK8,X0,X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1200,c_53])).

cnf(c_1205,plain,
    ( v5_pre_topc(sK8,X0,X1)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK3(X0,X1,sK8))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,k2_pre_topc(X1,sK3(X0,X1,sK8))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(renaming,[status(thm)],[c_1204])).

cnf(c_5282,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | v5_pre_topc(sK8,X1,X0) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK8,sK3(X1,X0,sK8))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK8,k2_pre_topc(X0,sK3(X1,X0,sK8)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1205])).

cnf(c_6090,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | v5_pre_topc(sK8,sK6,X0) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,sK3(sK6,X0,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,k2_pre_topc(X0,sK3(sK6,X0,sK8)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5282])).

cnf(c_5896,plain,
    ( v5_pre_topc(sK8,sK6,X0)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0))))
    | ~ r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,sK3(sK6,X0,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,k2_pre_topc(X0,sK3(sK6,X0,sK8))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK6)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1205])).

cnf(c_5897,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | v5_pre_topc(sK8,sK6,X0) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,sK3(sK6,X0,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,k2_pre_topc(X0,sK3(sK6,X0,sK8)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5896])).

cnf(c_6794,plain,
    ( l1_pre_topc(X0) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | v5_pre_topc(sK8,sK6,X0) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,sK3(sK6,X0,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,k2_pre_topc(X0,sK3(sK6,X0,sK8)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6090,c_59,c_61,c_5897,c_6243])).

cnf(c_6795,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | v5_pre_topc(sK8,sK6,X0) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,sK3(sK6,X0,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,k2_pre_topc(X0,sK3(sK6,X0,sK8)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6794])).

cnf(c_6806,plain,
    ( v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK3(sK6,sK7,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,k2_pre_topc(sK7,sK3(sK6,sK7,sK8)))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_6795])).

cnf(c_2473,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK3(X0,X1,sK8))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,k2_pre_topc(X1,sK3(X0,X1,sK8))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | sK7 != X1
    | sK6 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_50,c_1205])).

cnf(c_2474,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK3(sK6,sK7,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,k2_pre_topc(sK7,sK3(sK6,sK7,sK8))))
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_2473])).

cnf(c_2476,plain,
    ( ~ r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK3(sK6,sK7,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,k2_pre_topc(sK7,sK3(sK6,sK7,sK8))))
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2474,c_58,c_56,c_55,c_54,c_51])).

cnf(c_2478,plain,
    ( u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK3(sK6,sK7,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,k2_pre_topc(sK7,sK3(sK6,sK7,sK8)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2476])).

cnf(c_7181,plain,
    ( r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK3(sK6,sK7,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,k2_pre_topc(sK7,sK3(sK6,sK7,sK8)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6806,c_2478,c_6243,c_6575])).

cnf(c_11617,plain,
    ( r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,sK3(sK6,sK7,k1_xboole_0))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,k2_pre_topc(sK7,sK3(sK6,sK7,k1_xboole_0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11579,c_7181])).

cnf(c_19140,plain,
    ( r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,sK3(sK6,sK7,k1_xboole_0))),k8_relset_1(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK7,sK3(sK6,sK7,k1_xboole_0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11483,c_11617])).

cnf(c_24363,plain,
    ( r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK7,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18629,c_19140])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_5302,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8798,plain,
    ( k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,u1_struct_0(sK7)) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8) ),
    inference(superposition,[status(thm)],[c_5294,c_5302])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_5303,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7701,plain,
    ( k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_5294,c_5303])).

cnf(c_8810,plain,
    ( k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,u1_struct_0(sK7)) = k1_relat_1(sK8) ),
    inference(light_normalisation,[status(thm)],[c_8798,c_7701])).

cnf(c_5304,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_9537,plain,
    ( m1_subset_1(k1_relat_1(sK8),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8810,c_5304])).

cnf(c_10185,plain,
    ( m1_subset_1(k1_relat_1(sK8),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9537,c_66])).

cnf(c_49,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_31,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_805,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(resolution,[status(thm)],[c_49,c_31])).

cnf(c_43,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_819,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_805,c_43])).

cnf(c_5286,plain,
    ( k2_pre_topc(X0,X1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_10192,plain,
    ( k2_pre_topc(sK6,k1_relat_1(sK8)) = k1_relat_1(sK8)
    | v1_tdlat_3(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_10185,c_5286])).

cnf(c_60,plain,
    ( v1_tdlat_3(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_10476,plain,
    ( k2_pre_topc(sK6,k1_relat_1(sK8)) = k1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10192,c_60,c_61])).

cnf(c_11592,plain,
    ( k2_pre_topc(sK6,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_11579,c_10476])).

cnf(c_11601,plain,
    ( k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,u1_struct_0(sK7)) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_11579,c_8810])).

cnf(c_19161,plain,
    ( k8_relset_1(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_11483,c_11601])).

cnf(c_24384,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK7,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24363,c_11592,c_19161])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_5317,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10190,plain,
    ( r1_tarski(k1_relat_1(sK8),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10185,c_5308])).

cnf(c_10353,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10190,c_5316])).

cnf(c_11589,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11579,c_10353])).

cnf(c_16325,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
    | r2_hidden(sK1(k1_relat_1(k1_xboole_0),X0),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5317,c_11589])).

cnf(c_19,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_21,plain,
    ( v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_777,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_21])).

cnf(c_778,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_779,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f154])).

cnf(c_20,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_5306,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6418,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_5306])).

cnf(c_19043,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16325,c_779,c_6418])).

cnf(c_24586,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_24384,c_19043])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.45/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/1.52  
% 7.45/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.45/1.52  
% 7.45/1.52  ------  iProver source info
% 7.45/1.52  
% 7.45/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.45/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.45/1.52  git: non_committed_changes: false
% 7.45/1.52  git: last_make_outside_of_git: false
% 7.45/1.52  
% 7.45/1.52  ------ 
% 7.45/1.52  
% 7.45/1.52  ------ Input Options
% 7.45/1.52  
% 7.45/1.52  --out_options                           all
% 7.45/1.52  --tptp_safe_out                         true
% 7.45/1.52  --problem_path                          ""
% 7.45/1.52  --include_path                          ""
% 7.45/1.52  --clausifier                            res/vclausify_rel
% 7.45/1.52  --clausifier_options                    --mode clausify
% 7.45/1.52  --stdin                                 false
% 7.45/1.52  --stats_out                             all
% 7.45/1.52  
% 7.45/1.52  ------ General Options
% 7.45/1.52  
% 7.45/1.52  --fof                                   false
% 7.45/1.52  --time_out_real                         305.
% 7.45/1.52  --time_out_virtual                      -1.
% 7.45/1.52  --symbol_type_check                     false
% 7.45/1.52  --clausify_out                          false
% 7.45/1.52  --sig_cnt_out                           false
% 7.45/1.52  --trig_cnt_out                          false
% 7.45/1.52  --trig_cnt_out_tolerance                1.
% 7.45/1.52  --trig_cnt_out_sk_spl                   false
% 7.45/1.52  --abstr_cl_out                          false
% 7.45/1.52  
% 7.45/1.52  ------ Global Options
% 7.45/1.52  
% 7.45/1.52  --schedule                              default
% 7.45/1.52  --add_important_lit                     false
% 7.45/1.52  --prop_solver_per_cl                    1000
% 7.45/1.52  --min_unsat_core                        false
% 7.45/1.52  --soft_assumptions                      false
% 7.45/1.52  --soft_lemma_size                       3
% 7.45/1.52  --prop_impl_unit_size                   0
% 7.45/1.52  --prop_impl_unit                        []
% 7.45/1.52  --share_sel_clauses                     true
% 7.45/1.52  --reset_solvers                         false
% 7.45/1.52  --bc_imp_inh                            [conj_cone]
% 7.45/1.52  --conj_cone_tolerance                   3.
% 7.45/1.52  --extra_neg_conj                        none
% 7.45/1.52  --large_theory_mode                     true
% 7.45/1.52  --prolific_symb_bound                   200
% 7.45/1.52  --lt_threshold                          2000
% 7.45/1.52  --clause_weak_htbl                      true
% 7.45/1.52  --gc_record_bc_elim                     false
% 7.45/1.52  
% 7.45/1.52  ------ Preprocessing Options
% 7.45/1.52  
% 7.45/1.52  --preprocessing_flag                    true
% 7.45/1.52  --time_out_prep_mult                    0.1
% 7.45/1.52  --splitting_mode                        input
% 7.45/1.52  --splitting_grd                         true
% 7.45/1.52  --splitting_cvd                         false
% 7.45/1.52  --splitting_cvd_svl                     false
% 7.45/1.52  --splitting_nvd                         32
% 7.45/1.52  --sub_typing                            true
% 7.45/1.52  --prep_gs_sim                           true
% 7.45/1.52  --prep_unflatten                        true
% 7.45/1.52  --prep_res_sim                          true
% 7.45/1.52  --prep_upred                            true
% 7.45/1.52  --prep_sem_filter                       exhaustive
% 7.45/1.52  --prep_sem_filter_out                   false
% 7.45/1.52  --pred_elim                             true
% 7.45/1.52  --res_sim_input                         true
% 7.45/1.52  --eq_ax_congr_red                       true
% 7.45/1.52  --pure_diseq_elim                       true
% 7.45/1.52  --brand_transform                       false
% 7.45/1.52  --non_eq_to_eq                          false
% 7.45/1.52  --prep_def_merge                        true
% 7.45/1.52  --prep_def_merge_prop_impl              false
% 7.45/1.52  --prep_def_merge_mbd                    true
% 7.45/1.52  --prep_def_merge_tr_red                 false
% 7.45/1.52  --prep_def_merge_tr_cl                  false
% 7.45/1.52  --smt_preprocessing                     true
% 7.45/1.52  --smt_ac_axioms                         fast
% 7.45/1.52  --preprocessed_out                      false
% 7.45/1.52  --preprocessed_stats                    false
% 7.45/1.52  
% 7.45/1.52  ------ Abstraction refinement Options
% 7.45/1.52  
% 7.45/1.52  --abstr_ref                             []
% 7.45/1.52  --abstr_ref_prep                        false
% 7.45/1.52  --abstr_ref_until_sat                   false
% 7.45/1.52  --abstr_ref_sig_restrict                funpre
% 7.45/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.45/1.52  --abstr_ref_under                       []
% 7.45/1.52  
% 7.45/1.52  ------ SAT Options
% 7.45/1.52  
% 7.45/1.52  --sat_mode                              false
% 7.45/1.52  --sat_fm_restart_options                ""
% 7.45/1.52  --sat_gr_def                            false
% 7.45/1.52  --sat_epr_types                         true
% 7.45/1.52  --sat_non_cyclic_types                  false
% 7.45/1.52  --sat_finite_models                     false
% 7.45/1.52  --sat_fm_lemmas                         false
% 7.45/1.52  --sat_fm_prep                           false
% 7.45/1.52  --sat_fm_uc_incr                        true
% 7.45/1.52  --sat_out_model                         small
% 7.45/1.52  --sat_out_clauses                       false
% 7.45/1.52  
% 7.45/1.52  ------ QBF Options
% 7.45/1.52  
% 7.45/1.52  --qbf_mode                              false
% 7.45/1.52  --qbf_elim_univ                         false
% 7.45/1.52  --qbf_dom_inst                          none
% 7.45/1.52  --qbf_dom_pre_inst                      false
% 7.45/1.52  --qbf_sk_in                             false
% 7.45/1.52  --qbf_pred_elim                         true
% 7.45/1.52  --qbf_split                             512
% 7.45/1.52  
% 7.45/1.52  ------ BMC1 Options
% 7.45/1.52  
% 7.45/1.52  --bmc1_incremental                      false
% 7.45/1.52  --bmc1_axioms                           reachable_all
% 7.45/1.52  --bmc1_min_bound                        0
% 7.45/1.52  --bmc1_max_bound                        -1
% 7.45/1.52  --bmc1_max_bound_default                -1
% 7.45/1.52  --bmc1_symbol_reachability              true
% 7.45/1.52  --bmc1_property_lemmas                  false
% 7.45/1.52  --bmc1_k_induction                      false
% 7.45/1.52  --bmc1_non_equiv_states                 false
% 7.45/1.52  --bmc1_deadlock                         false
% 7.45/1.52  --bmc1_ucm                              false
% 7.45/1.52  --bmc1_add_unsat_core                   none
% 7.45/1.52  --bmc1_unsat_core_children              false
% 7.45/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.45/1.52  --bmc1_out_stat                         full
% 7.45/1.52  --bmc1_ground_init                      false
% 7.45/1.52  --bmc1_pre_inst_next_state              false
% 7.45/1.52  --bmc1_pre_inst_state                   false
% 7.45/1.52  --bmc1_pre_inst_reach_state             false
% 7.45/1.52  --bmc1_out_unsat_core                   false
% 7.45/1.52  --bmc1_aig_witness_out                  false
% 7.45/1.52  --bmc1_verbose                          false
% 7.45/1.52  --bmc1_dump_clauses_tptp                false
% 7.45/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.45/1.52  --bmc1_dump_file                        -
% 7.45/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.45/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.45/1.52  --bmc1_ucm_extend_mode                  1
% 7.45/1.52  --bmc1_ucm_init_mode                    2
% 7.45/1.52  --bmc1_ucm_cone_mode                    none
% 7.45/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.45/1.52  --bmc1_ucm_relax_model                  4
% 7.45/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.45/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.45/1.52  --bmc1_ucm_layered_model                none
% 7.45/1.52  --bmc1_ucm_max_lemma_size               10
% 7.45/1.52  
% 7.45/1.52  ------ AIG Options
% 7.45/1.52  
% 7.45/1.52  --aig_mode                              false
% 7.45/1.52  
% 7.45/1.52  ------ Instantiation Options
% 7.45/1.52  
% 7.45/1.52  --instantiation_flag                    true
% 7.45/1.52  --inst_sos_flag                         false
% 7.45/1.52  --inst_sos_phase                        true
% 7.45/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.45/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.45/1.52  --inst_lit_sel_side                     num_symb
% 7.45/1.52  --inst_solver_per_active                1400
% 7.45/1.52  --inst_solver_calls_frac                1.
% 7.45/1.52  --inst_passive_queue_type               priority_queues
% 7.45/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.45/1.52  --inst_passive_queues_freq              [25;2]
% 7.45/1.52  --inst_dismatching                      true
% 7.45/1.52  --inst_eager_unprocessed_to_passive     true
% 7.45/1.52  --inst_prop_sim_given                   true
% 7.45/1.52  --inst_prop_sim_new                     false
% 7.45/1.52  --inst_subs_new                         false
% 7.45/1.52  --inst_eq_res_simp                      false
% 7.45/1.52  --inst_subs_given                       false
% 7.45/1.52  --inst_orphan_elimination               true
% 7.45/1.52  --inst_learning_loop_flag               true
% 7.45/1.52  --inst_learning_start                   3000
% 7.45/1.52  --inst_learning_factor                  2
% 7.45/1.52  --inst_start_prop_sim_after_learn       3
% 7.45/1.52  --inst_sel_renew                        solver
% 7.45/1.52  --inst_lit_activity_flag                true
% 7.45/1.52  --inst_restr_to_given                   false
% 7.45/1.52  --inst_activity_threshold               500
% 7.45/1.52  --inst_out_proof                        true
% 7.45/1.52  
% 7.45/1.52  ------ Resolution Options
% 7.45/1.52  
% 7.45/1.52  --resolution_flag                       true
% 7.45/1.52  --res_lit_sel                           adaptive
% 7.45/1.52  --res_lit_sel_side                      none
% 7.45/1.52  --res_ordering                          kbo
% 7.45/1.52  --res_to_prop_solver                    active
% 7.45/1.52  --res_prop_simpl_new                    false
% 7.45/1.52  --res_prop_simpl_given                  true
% 7.45/1.52  --res_passive_queue_type                priority_queues
% 7.45/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.45/1.52  --res_passive_queues_freq               [15;5]
% 7.45/1.52  --res_forward_subs                      full
% 7.45/1.52  --res_backward_subs                     full
% 7.45/1.52  --res_forward_subs_resolution           true
% 7.45/1.52  --res_backward_subs_resolution          true
% 7.45/1.52  --res_orphan_elimination                true
% 7.45/1.52  --res_time_limit                        2.
% 7.45/1.52  --res_out_proof                         true
% 7.45/1.52  
% 7.45/1.52  ------ Superposition Options
% 7.45/1.52  
% 7.45/1.52  --superposition_flag                    true
% 7.45/1.52  --sup_passive_queue_type                priority_queues
% 7.45/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.45/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.45/1.52  --demod_completeness_check              fast
% 7.45/1.52  --demod_use_ground                      true
% 7.45/1.52  --sup_to_prop_solver                    passive
% 7.45/1.52  --sup_prop_simpl_new                    true
% 7.45/1.52  --sup_prop_simpl_given                  true
% 7.45/1.52  --sup_fun_splitting                     false
% 7.45/1.52  --sup_smt_interval                      50000
% 7.45/1.52  
% 7.45/1.52  ------ Superposition Simplification Setup
% 7.45/1.52  
% 7.45/1.52  --sup_indices_passive                   []
% 7.45/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.45/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.45/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.45/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.45/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.45/1.52  --sup_full_bw                           [BwDemod]
% 7.45/1.52  --sup_immed_triv                        [TrivRules]
% 7.45/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.45/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.45/1.52  --sup_immed_bw_main                     []
% 7.45/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.45/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.45/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.45/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.45/1.52  
% 7.45/1.52  ------ Combination Options
% 7.45/1.52  
% 7.45/1.52  --comb_res_mult                         3
% 7.45/1.52  --comb_sup_mult                         2
% 7.45/1.52  --comb_inst_mult                        10
% 7.45/1.52  
% 7.45/1.52  ------ Debug Options
% 7.45/1.52  
% 7.45/1.52  --dbg_backtrace                         false
% 7.45/1.52  --dbg_dump_prop_clauses                 false
% 7.45/1.52  --dbg_dump_prop_clauses_file            -
% 7.45/1.52  --dbg_out_stat                          false
% 7.45/1.52  ------ Parsing...
% 7.45/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.45/1.52  
% 7.45/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.45/1.52  
% 7.45/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.45/1.52  
% 7.45/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.45/1.52  ------ Proving...
% 7.45/1.52  ------ Problem Properties 
% 7.45/1.52  
% 7.45/1.52  
% 7.45/1.52  clauses                                 50
% 7.45/1.52  conjectures                             7
% 7.45/1.52  EPR                                     14
% 7.45/1.52  Horn                                    38
% 7.45/1.52  unary                                   14
% 7.45/1.52  binary                                  12
% 7.45/1.52  lits                                    180
% 7.45/1.52  lits eq                                 42
% 7.45/1.52  fd_pure                                 0
% 7.45/1.52  fd_pseudo                               0
% 7.45/1.52  fd_cond                                 2
% 7.45/1.52  fd_pseudo_cond                          1
% 7.45/1.52  AC symbols                              0
% 7.45/1.52  
% 7.45/1.52  ------ Schedule dynamic 5 is on 
% 7.45/1.52  
% 7.45/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.45/1.52  
% 7.45/1.52  
% 7.45/1.52  ------ 
% 7.45/1.52  Current options:
% 7.45/1.52  ------ 
% 7.45/1.52  
% 7.45/1.52  ------ Input Options
% 7.45/1.52  
% 7.45/1.52  --out_options                           all
% 7.45/1.52  --tptp_safe_out                         true
% 7.45/1.52  --problem_path                          ""
% 7.45/1.52  --include_path                          ""
% 7.45/1.52  --clausifier                            res/vclausify_rel
% 7.45/1.52  --clausifier_options                    --mode clausify
% 7.45/1.52  --stdin                                 false
% 7.45/1.52  --stats_out                             all
% 7.45/1.52  
% 7.45/1.52  ------ General Options
% 7.45/1.52  
% 7.45/1.52  --fof                                   false
% 7.45/1.52  --time_out_real                         305.
% 7.45/1.52  --time_out_virtual                      -1.
% 7.45/1.52  --symbol_type_check                     false
% 7.45/1.52  --clausify_out                          false
% 7.45/1.52  --sig_cnt_out                           false
% 7.45/1.52  --trig_cnt_out                          false
% 7.45/1.52  --trig_cnt_out_tolerance                1.
% 7.45/1.52  --trig_cnt_out_sk_spl                   false
% 7.45/1.52  --abstr_cl_out                          false
% 7.45/1.52  
% 7.45/1.52  ------ Global Options
% 7.45/1.52  
% 7.45/1.52  --schedule                              default
% 7.45/1.52  --add_important_lit                     false
% 7.45/1.52  --prop_solver_per_cl                    1000
% 7.45/1.52  --min_unsat_core                        false
% 7.45/1.52  --soft_assumptions                      false
% 7.45/1.52  --soft_lemma_size                       3
% 7.45/1.52  --prop_impl_unit_size                   0
% 7.45/1.52  --prop_impl_unit                        []
% 7.45/1.52  --share_sel_clauses                     true
% 7.45/1.52  --reset_solvers                         false
% 7.45/1.52  --bc_imp_inh                            [conj_cone]
% 7.45/1.52  --conj_cone_tolerance                   3.
% 7.45/1.52  --extra_neg_conj                        none
% 7.45/1.52  --large_theory_mode                     true
% 7.45/1.52  --prolific_symb_bound                   200
% 7.45/1.52  --lt_threshold                          2000
% 7.45/1.52  --clause_weak_htbl                      true
% 7.45/1.52  --gc_record_bc_elim                     false
% 7.45/1.52  
% 7.45/1.52  ------ Preprocessing Options
% 7.45/1.52  
% 7.45/1.52  --preprocessing_flag                    true
% 7.45/1.52  --time_out_prep_mult                    0.1
% 7.45/1.52  --splitting_mode                        input
% 7.45/1.52  --splitting_grd                         true
% 7.45/1.52  --splitting_cvd                         false
% 7.45/1.52  --splitting_cvd_svl                     false
% 7.45/1.52  --splitting_nvd                         32
% 7.45/1.52  --sub_typing                            true
% 7.45/1.52  --prep_gs_sim                           true
% 7.45/1.52  --prep_unflatten                        true
% 7.45/1.52  --prep_res_sim                          true
% 7.45/1.52  --prep_upred                            true
% 7.45/1.52  --prep_sem_filter                       exhaustive
% 7.45/1.52  --prep_sem_filter_out                   false
% 7.45/1.52  --pred_elim                             true
% 7.45/1.52  --res_sim_input                         true
% 7.45/1.52  --eq_ax_congr_red                       true
% 7.45/1.52  --pure_diseq_elim                       true
% 7.45/1.52  --brand_transform                       false
% 7.45/1.52  --non_eq_to_eq                          false
% 7.45/1.52  --prep_def_merge                        true
% 7.45/1.52  --prep_def_merge_prop_impl              false
% 7.45/1.52  --prep_def_merge_mbd                    true
% 7.45/1.52  --prep_def_merge_tr_red                 false
% 7.45/1.52  --prep_def_merge_tr_cl                  false
% 7.45/1.52  --smt_preprocessing                     true
% 7.45/1.52  --smt_ac_axioms                         fast
% 7.45/1.52  --preprocessed_out                      false
% 7.45/1.52  --preprocessed_stats                    false
% 7.45/1.52  
% 7.45/1.52  ------ Abstraction refinement Options
% 7.45/1.52  
% 7.45/1.52  --abstr_ref                             []
% 7.45/1.52  --abstr_ref_prep                        false
% 7.45/1.52  --abstr_ref_until_sat                   false
% 7.45/1.52  --abstr_ref_sig_restrict                funpre
% 7.45/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.45/1.52  --abstr_ref_under                       []
% 7.45/1.52  
% 7.45/1.52  ------ SAT Options
% 7.45/1.52  
% 7.45/1.52  --sat_mode                              false
% 7.45/1.52  --sat_fm_restart_options                ""
% 7.45/1.52  --sat_gr_def                            false
% 7.45/1.52  --sat_epr_types                         true
% 7.45/1.52  --sat_non_cyclic_types                  false
% 7.45/1.52  --sat_finite_models                     false
% 7.45/1.52  --sat_fm_lemmas                         false
% 7.45/1.52  --sat_fm_prep                           false
% 7.45/1.52  --sat_fm_uc_incr                        true
% 7.45/1.52  --sat_out_model                         small
% 7.45/1.52  --sat_out_clauses                       false
% 7.45/1.52  
% 7.45/1.52  ------ QBF Options
% 7.45/1.52  
% 7.45/1.52  --qbf_mode                              false
% 7.45/1.52  --qbf_elim_univ                         false
% 7.45/1.52  --qbf_dom_inst                          none
% 7.45/1.52  --qbf_dom_pre_inst                      false
% 7.45/1.52  --qbf_sk_in                             false
% 7.45/1.52  --qbf_pred_elim                         true
% 7.45/1.52  --qbf_split                             512
% 7.45/1.52  
% 7.45/1.52  ------ BMC1 Options
% 7.45/1.52  
% 7.45/1.52  --bmc1_incremental                      false
% 7.45/1.52  --bmc1_axioms                           reachable_all
% 7.45/1.52  --bmc1_min_bound                        0
% 7.45/1.52  --bmc1_max_bound                        -1
% 7.45/1.52  --bmc1_max_bound_default                -1
% 7.45/1.52  --bmc1_symbol_reachability              true
% 7.45/1.52  --bmc1_property_lemmas                  false
% 7.45/1.52  --bmc1_k_induction                      false
% 7.45/1.52  --bmc1_non_equiv_states                 false
% 7.45/1.52  --bmc1_deadlock                         false
% 7.45/1.52  --bmc1_ucm                              false
% 7.45/1.52  --bmc1_add_unsat_core                   none
% 7.45/1.52  --bmc1_unsat_core_children              false
% 7.45/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.45/1.52  --bmc1_out_stat                         full
% 7.45/1.52  --bmc1_ground_init                      false
% 7.45/1.52  --bmc1_pre_inst_next_state              false
% 7.45/1.52  --bmc1_pre_inst_state                   false
% 7.45/1.52  --bmc1_pre_inst_reach_state             false
% 7.45/1.52  --bmc1_out_unsat_core                   false
% 7.45/1.52  --bmc1_aig_witness_out                  false
% 7.45/1.52  --bmc1_verbose                          false
% 7.45/1.52  --bmc1_dump_clauses_tptp                false
% 7.45/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.45/1.52  --bmc1_dump_file                        -
% 7.45/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.45/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.45/1.52  --bmc1_ucm_extend_mode                  1
% 7.45/1.52  --bmc1_ucm_init_mode                    2
% 7.45/1.52  --bmc1_ucm_cone_mode                    none
% 7.45/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.45/1.52  --bmc1_ucm_relax_model                  4
% 7.45/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.45/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.45/1.52  --bmc1_ucm_layered_model                none
% 7.45/1.52  --bmc1_ucm_max_lemma_size               10
% 7.45/1.52  
% 7.45/1.52  ------ AIG Options
% 7.45/1.52  
% 7.45/1.52  --aig_mode                              false
% 7.45/1.52  
% 7.45/1.52  ------ Instantiation Options
% 7.45/1.52  
% 7.45/1.52  --instantiation_flag                    true
% 7.45/1.52  --inst_sos_flag                         false
% 7.45/1.52  --inst_sos_phase                        true
% 7.45/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.45/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.45/1.52  --inst_lit_sel_side                     none
% 7.45/1.52  --inst_solver_per_active                1400
% 7.45/1.52  --inst_solver_calls_frac                1.
% 7.45/1.52  --inst_passive_queue_type               priority_queues
% 7.45/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.45/1.52  --inst_passive_queues_freq              [25;2]
% 7.45/1.52  --inst_dismatching                      true
% 7.45/1.52  --inst_eager_unprocessed_to_passive     true
% 7.45/1.52  --inst_prop_sim_given                   true
% 7.45/1.52  --inst_prop_sim_new                     false
% 7.45/1.52  --inst_subs_new                         false
% 7.45/1.52  --inst_eq_res_simp                      false
% 7.45/1.52  --inst_subs_given                       false
% 7.45/1.52  --inst_orphan_elimination               true
% 7.45/1.52  --inst_learning_loop_flag               true
% 7.45/1.52  --inst_learning_start                   3000
% 7.45/1.52  --inst_learning_factor                  2
% 7.45/1.52  --inst_start_prop_sim_after_learn       3
% 7.45/1.52  --inst_sel_renew                        solver
% 7.45/1.52  --inst_lit_activity_flag                true
% 7.45/1.52  --inst_restr_to_given                   false
% 7.45/1.52  --inst_activity_threshold               500
% 7.45/1.52  --inst_out_proof                        true
% 7.45/1.52  
% 7.45/1.52  ------ Resolution Options
% 7.45/1.52  
% 7.45/1.52  --resolution_flag                       false
% 7.45/1.52  --res_lit_sel                           adaptive
% 7.45/1.52  --res_lit_sel_side                      none
% 7.45/1.52  --res_ordering                          kbo
% 7.45/1.52  --res_to_prop_solver                    active
% 7.45/1.52  --res_prop_simpl_new                    false
% 7.45/1.52  --res_prop_simpl_given                  true
% 7.45/1.52  --res_passive_queue_type                priority_queues
% 7.45/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.45/1.52  --res_passive_queues_freq               [15;5]
% 7.45/1.52  --res_forward_subs                      full
% 7.45/1.52  --res_backward_subs                     full
% 7.45/1.52  --res_forward_subs_resolution           true
% 7.45/1.52  --res_backward_subs_resolution          true
% 7.45/1.52  --res_orphan_elimination                true
% 7.45/1.52  --res_time_limit                        2.
% 7.45/1.52  --res_out_proof                         true
% 7.45/1.52  
% 7.45/1.52  ------ Superposition Options
% 7.45/1.52  
% 7.45/1.52  --superposition_flag                    true
% 7.45/1.52  --sup_passive_queue_type                priority_queues
% 7.45/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.45/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.45/1.52  --demod_completeness_check              fast
% 7.45/1.52  --demod_use_ground                      true
% 7.45/1.52  --sup_to_prop_solver                    passive
% 7.45/1.52  --sup_prop_simpl_new                    true
% 7.45/1.52  --sup_prop_simpl_given                  true
% 7.45/1.52  --sup_fun_splitting                     false
% 7.45/1.52  --sup_smt_interval                      50000
% 7.45/1.52  
% 7.45/1.52  ------ Superposition Simplification Setup
% 7.45/1.52  
% 7.45/1.52  --sup_indices_passive                   []
% 7.45/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.45/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.45/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.45/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.45/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.45/1.52  --sup_full_bw                           [BwDemod]
% 7.45/1.52  --sup_immed_triv                        [TrivRules]
% 7.45/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.45/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.45/1.52  --sup_immed_bw_main                     []
% 7.45/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.45/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.45/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.45/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.45/1.52  
% 7.45/1.52  ------ Combination Options
% 7.45/1.52  
% 7.45/1.52  --comb_res_mult                         3
% 7.45/1.52  --comb_sup_mult                         2
% 7.45/1.52  --comb_inst_mult                        10
% 7.45/1.52  
% 7.45/1.52  ------ Debug Options
% 7.45/1.52  
% 7.45/1.52  --dbg_backtrace                         false
% 7.45/1.52  --dbg_dump_prop_clauses                 false
% 7.45/1.52  --dbg_dump_prop_clauses_file            -
% 7.45/1.52  --dbg_out_stat                          false
% 7.45/1.52  
% 7.45/1.52  
% 7.45/1.52  
% 7.45/1.52  
% 7.45/1.52  ------ Proving...
% 7.45/1.52  
% 7.45/1.52  
% 7.45/1.52  % SZS status Theorem for theBenchmark.p
% 7.45/1.52  
% 7.45/1.52   Resolution empty clause
% 7.45/1.52  
% 7.45/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.45/1.52  
% 7.45/1.52  fof(f22,axiom,(
% 7.45/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f46,plain,(
% 7.45/1.52    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.45/1.52    inference(ennf_transformation,[],[f22])).
% 7.45/1.52  
% 7.45/1.52  fof(f47,plain,(
% 7.45/1.52    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.45/1.52    inference(flattening,[],[f46])).
% 7.45/1.52  
% 7.45/1.52  fof(f73,plain,(
% 7.45/1.52    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.45/1.52    inference(nnf_transformation,[],[f47])).
% 7.45/1.52  
% 7.45/1.52  fof(f74,plain,(
% 7.45/1.52    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.45/1.52    inference(rectify,[],[f73])).
% 7.45/1.52  
% 7.45/1.52  fof(f75,plain,(
% 7.45/1.52    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v3_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 7.45/1.52    introduced(choice_axiom,[])).
% 7.45/1.52  
% 7.45/1.52  fof(f76,plain,(
% 7.45/1.52    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v3_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.45/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f74,f75])).
% 7.45/1.52  
% 7.45/1.52  fof(f127,plain,(
% 7.45/1.52    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f76])).
% 7.45/1.52  
% 7.45/1.52  fof(f27,conjecture,(
% 7.45/1.52    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f28,negated_conjecture,(
% 7.45/1.52    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 7.45/1.52    inference(negated_conjecture,[],[f27])).
% 7.45/1.52  
% 7.45/1.52  fof(f56,plain,(
% 7.45/1.52    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)))),
% 7.45/1.52    inference(ennf_transformation,[],[f28])).
% 7.45/1.52  
% 7.45/1.52  fof(f57,plain,(
% 7.45/1.52    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0))),
% 7.45/1.52    inference(flattening,[],[f56])).
% 7.45/1.52  
% 7.45/1.52  fof(f91,plain,(
% 7.45/1.52    ( ! [X0,X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~v5_pre_topc(sK8,X0,X1) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 7.45/1.52    introduced(choice_axiom,[])).
% 7.45/1.52  
% 7.45/1.52  fof(f90,plain,(
% 7.45/1.52    ( ! [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (~v5_pre_topc(X2,X0,sK7) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK7)) & v1_funct_1(X2)) & l1_pre_topc(sK7) & v2_pre_topc(sK7))) )),
% 7.45/1.52    introduced(choice_axiom,[])).
% 7.45/1.52  
% 7.45/1.52  fof(f89,plain,(
% 7.45/1.52    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v5_pre_topc(X2,sK6,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK6) & v1_tdlat_3(sK6) & v2_pre_topc(sK6))),
% 7.45/1.52    introduced(choice_axiom,[])).
% 7.45/1.52  
% 7.45/1.52  fof(f92,plain,(
% 7.45/1.52    ((~v5_pre_topc(sK8,sK6,sK7) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(sK8)) & l1_pre_topc(sK7) & v2_pre_topc(sK7)) & l1_pre_topc(sK6) & v1_tdlat_3(sK6) & v2_pre_topc(sK6)),
% 7.45/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f57,f91,f90,f89])).
% 7.45/1.52  
% 7.45/1.52  fof(f149,plain,(
% 7.45/1.52    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))),
% 7.45/1.52    inference(cnf_transformation,[],[f92])).
% 7.45/1.52  
% 7.45/1.52  fof(f148,plain,(
% 7.45/1.52    v1_funct_1(sK8)),
% 7.45/1.52    inference(cnf_transformation,[],[f92])).
% 7.45/1.52  
% 7.45/1.52  fof(f145,plain,(
% 7.45/1.52    l1_pre_topc(sK6)),
% 7.45/1.52    inference(cnf_transformation,[],[f92])).
% 7.45/1.52  
% 7.45/1.52  fof(f147,plain,(
% 7.45/1.52    l1_pre_topc(sK7)),
% 7.45/1.52    inference(cnf_transformation,[],[f92])).
% 7.45/1.52  
% 7.45/1.52  fof(f150,plain,(
% 7.45/1.52    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 7.45/1.52    inference(cnf_transformation,[],[f92])).
% 7.45/1.52  
% 7.45/1.52  fof(f151,plain,(
% 7.45/1.52    ~v5_pre_topc(sK8,sK6,sK7)),
% 7.45/1.52    inference(cnf_transformation,[],[f92])).
% 7.45/1.52  
% 7.45/1.52  fof(f10,axiom,(
% 7.45/1.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f32,plain,(
% 7.45/1.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.45/1.52    inference(ennf_transformation,[],[f10])).
% 7.45/1.52  
% 7.45/1.52  fof(f33,plain,(
% 7.45/1.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.45/1.52    inference(flattening,[],[f32])).
% 7.45/1.52  
% 7.45/1.52  fof(f110,plain,(
% 7.45/1.52    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f33])).
% 7.45/1.52  
% 7.45/1.52  fof(f143,plain,(
% 7.45/1.52    v2_pre_topc(sK6)),
% 7.45/1.52    inference(cnf_transformation,[],[f92])).
% 7.45/1.52  
% 7.45/1.52  fof(f144,plain,(
% 7.45/1.52    v1_tdlat_3(sK6)),
% 7.45/1.52    inference(cnf_transformation,[],[f92])).
% 7.45/1.52  
% 7.45/1.52  fof(f131,plain,(
% 7.45/1.52    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f76])).
% 7.45/1.52  
% 7.45/1.52  fof(f25,axiom,(
% 7.45/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f52,plain,(
% 7.45/1.52    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.45/1.52    inference(ennf_transformation,[],[f25])).
% 7.45/1.52  
% 7.45/1.52  fof(f53,plain,(
% 7.45/1.52    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.52    inference(flattening,[],[f52])).
% 7.45/1.52  
% 7.45/1.52  fof(f81,plain,(
% 7.45/1.52    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.52    inference(nnf_transformation,[],[f53])).
% 7.45/1.52  
% 7.45/1.52  fof(f82,plain,(
% 7.45/1.52    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.52    inference(rectify,[],[f81])).
% 7.45/1.52  
% 7.45/1.52  fof(f83,plain,(
% 7.45/1.52    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.45/1.52    introduced(choice_axiom,[])).
% 7.45/1.52  
% 7.45/1.52  fof(f84,plain,(
% 7.45/1.52    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f82,f83])).
% 7.45/1.52  
% 7.45/1.52  fof(f137,plain,(
% 7.45/1.52    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f84])).
% 7.45/1.52  
% 7.45/1.52  fof(f15,axiom,(
% 7.45/1.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f36,plain,(
% 7.45/1.52    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.45/1.52    inference(ennf_transformation,[],[f15])).
% 7.45/1.52  
% 7.45/1.52  fof(f116,plain,(
% 7.45/1.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.45/1.52    inference(cnf_transformation,[],[f36])).
% 7.45/1.52  
% 7.45/1.52  fof(f18,axiom,(
% 7.45/1.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f39,plain,(
% 7.45/1.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.45/1.52    inference(ennf_transformation,[],[f18])).
% 7.45/1.52  
% 7.45/1.52  fof(f120,plain,(
% 7.45/1.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f39])).
% 7.45/1.52  
% 7.45/1.52  fof(f20,axiom,(
% 7.45/1.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f42,plain,(
% 7.45/1.52    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.45/1.52    inference(ennf_transformation,[],[f20])).
% 7.45/1.52  
% 7.45/1.52  fof(f43,plain,(
% 7.45/1.52    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.45/1.52    inference(flattening,[],[f42])).
% 7.45/1.52  
% 7.45/1.52  fof(f122,plain,(
% 7.45/1.52    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f43])).
% 7.45/1.52  
% 7.45/1.52  fof(f19,axiom,(
% 7.45/1.52    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f40,plain,(
% 7.45/1.52    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 7.45/1.52    inference(ennf_transformation,[],[f19])).
% 7.45/1.52  
% 7.45/1.52  fof(f41,plain,(
% 7.45/1.52    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 7.45/1.52    inference(flattening,[],[f40])).
% 7.45/1.52  
% 7.45/1.52  fof(f121,plain,(
% 7.45/1.52    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f41])).
% 7.45/1.52  
% 7.45/1.52  fof(f3,axiom,(
% 7.45/1.52    v1_xboole_0(k1_xboole_0)),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f98,plain,(
% 7.45/1.52    v1_xboole_0(k1_xboole_0)),
% 7.45/1.52    inference(cnf_transformation,[],[f3])).
% 7.45/1.52  
% 7.45/1.52  fof(f14,axiom,(
% 7.45/1.52    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f35,plain,(
% 7.45/1.52    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 7.45/1.52    inference(ennf_transformation,[],[f14])).
% 7.45/1.52  
% 7.45/1.52  fof(f115,plain,(
% 7.45/1.52    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f35])).
% 7.45/1.52  
% 7.45/1.52  fof(f4,axiom,(
% 7.45/1.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f31,plain,(
% 7.45/1.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.45/1.52    inference(ennf_transformation,[],[f4])).
% 7.45/1.52  
% 7.45/1.52  fof(f99,plain,(
% 7.45/1.52    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f31])).
% 7.45/1.52  
% 7.45/1.52  fof(f1,axiom,(
% 7.45/1.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f58,plain,(
% 7.45/1.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.45/1.52    inference(nnf_transformation,[],[f1])).
% 7.45/1.52  
% 7.45/1.52  fof(f59,plain,(
% 7.45/1.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.45/1.52    inference(rectify,[],[f58])).
% 7.45/1.52  
% 7.45/1.52  fof(f60,plain,(
% 7.45/1.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.45/1.52    introduced(choice_axiom,[])).
% 7.45/1.52  
% 7.45/1.52  fof(f61,plain,(
% 7.45/1.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.45/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f59,f60])).
% 7.45/1.52  
% 7.45/1.52  fof(f94,plain,(
% 7.45/1.52    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f61])).
% 7.45/1.52  
% 7.45/1.52  fof(f23,axiom,(
% 7.45/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f48,plain,(
% 7.45/1.52    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.45/1.52    inference(ennf_transformation,[],[f23])).
% 7.45/1.52  
% 7.45/1.52  fof(f49,plain,(
% 7.45/1.52    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.52    inference(flattening,[],[f48])).
% 7.45/1.52  
% 7.45/1.52  fof(f77,plain,(
% 7.45/1.52    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.52    inference(nnf_transformation,[],[f49])).
% 7.45/1.52  
% 7.45/1.52  fof(f78,plain,(
% 7.45/1.52    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.52    inference(rectify,[],[f77])).
% 7.45/1.52  
% 7.45/1.52  fof(f79,plain,(
% 7.45/1.52    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2)))) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 7.45/1.52    introduced(choice_axiom,[])).
% 7.45/1.52  
% 7.45/1.52  fof(f80,plain,(
% 7.45/1.52    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2)))) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f78,f79])).
% 7.45/1.52  
% 7.45/1.52  fof(f134,plain,(
% 7.45/1.52    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f80])).
% 7.45/1.52  
% 7.45/1.52  fof(f146,plain,(
% 7.45/1.52    v2_pre_topc(sK7)),
% 7.45/1.52    inference(cnf_transformation,[],[f92])).
% 7.45/1.52  
% 7.45/1.52  fof(f9,axiom,(
% 7.45/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f70,plain,(
% 7.45/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.45/1.52    inference(nnf_transformation,[],[f9])).
% 7.45/1.52  
% 7.45/1.52  fof(f108,plain,(
% 7.45/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.45/1.52    inference(cnf_transformation,[],[f70])).
% 7.45/1.52  
% 7.45/1.52  fof(f2,axiom,(
% 7.45/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f30,plain,(
% 7.45/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.45/1.52    inference(ennf_transformation,[],[f2])).
% 7.45/1.52  
% 7.45/1.52  fof(f62,plain,(
% 7.45/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.45/1.52    inference(nnf_transformation,[],[f30])).
% 7.45/1.52  
% 7.45/1.52  fof(f63,plain,(
% 7.45/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.45/1.52    inference(rectify,[],[f62])).
% 7.45/1.52  
% 7.45/1.52  fof(f64,plain,(
% 7.45/1.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.45/1.52    introduced(choice_axiom,[])).
% 7.45/1.52  
% 7.45/1.52  fof(f65,plain,(
% 7.45/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.45/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f63,f64])).
% 7.45/1.52  
% 7.45/1.52  fof(f95,plain,(
% 7.45/1.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f65])).
% 7.45/1.52  
% 7.45/1.52  fof(f93,plain,(
% 7.45/1.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f61])).
% 7.45/1.52  
% 7.45/1.52  fof(f135,plain,(
% 7.45/1.52    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f80])).
% 7.45/1.52  
% 7.45/1.52  fof(f17,axiom,(
% 7.45/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f38,plain,(
% 7.45/1.52    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.45/1.52    inference(ennf_transformation,[],[f17])).
% 7.45/1.52  
% 7.45/1.52  fof(f119,plain,(
% 7.45/1.52    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.45/1.52    inference(cnf_transformation,[],[f38])).
% 7.45/1.52  
% 7.45/1.52  fof(f16,axiom,(
% 7.45/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f37,plain,(
% 7.45/1.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.45/1.52    inference(ennf_transformation,[],[f16])).
% 7.45/1.52  
% 7.45/1.52  fof(f117,plain,(
% 7.45/1.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.45/1.52    inference(cnf_transformation,[],[f37])).
% 7.45/1.52  
% 7.45/1.52  fof(f26,axiom,(
% 7.45/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v4_pre_topc(X1,X0))))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f54,plain,(
% 7.45/1.52    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.45/1.52    inference(ennf_transformation,[],[f26])).
% 7.45/1.52  
% 7.45/1.52  fof(f55,plain,(
% 7.45/1.52    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.52    inference(flattening,[],[f54])).
% 7.45/1.52  
% 7.45/1.52  fof(f85,plain,(
% 7.45/1.52    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.52    inference(nnf_transformation,[],[f55])).
% 7.45/1.52  
% 7.45/1.52  fof(f86,plain,(
% 7.45/1.52    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.52    inference(rectify,[],[f85])).
% 7.45/1.52  
% 7.45/1.52  fof(f87,plain,(
% 7.45/1.52    ! [X0] : (? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.45/1.52    introduced(choice_axiom,[])).
% 7.45/1.52  
% 7.45/1.52  fof(f88,plain,(
% 7.45/1.52    ! [X0] : (((v1_tdlat_3(X0) | (~v4_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f86,f87])).
% 7.45/1.52  
% 7.45/1.52  fof(f140,plain,(
% 7.45/1.52    ( ! [X2,X0] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f88])).
% 7.45/1.52  
% 7.45/1.52  fof(f21,axiom,(
% 7.45/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f44,plain,(
% 7.45/1.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.45/1.52    inference(ennf_transformation,[],[f21])).
% 7.45/1.52  
% 7.45/1.52  fof(f45,plain,(
% 7.45/1.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.45/1.52    inference(flattening,[],[f44])).
% 7.45/1.52  
% 7.45/1.52  fof(f123,plain,(
% 7.45/1.52    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f45])).
% 7.45/1.52  
% 7.45/1.52  fof(f24,axiom,(
% 7.45/1.52    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f50,plain,(
% 7.45/1.52    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 7.45/1.52    inference(ennf_transformation,[],[f24])).
% 7.45/1.52  
% 7.45/1.52  fof(f51,plain,(
% 7.45/1.52    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 7.45/1.52    inference(flattening,[],[f50])).
% 7.45/1.52  
% 7.45/1.52  fof(f136,plain,(
% 7.45/1.52    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f51])).
% 7.45/1.52  
% 7.45/1.52  fof(f96,plain,(
% 7.45/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f65])).
% 7.45/1.52  
% 7.45/1.52  fof(f11,axiom,(
% 7.45/1.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f34,plain,(
% 7.45/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.45/1.52    inference(ennf_transformation,[],[f11])).
% 7.45/1.52  
% 7.45/1.52  fof(f71,plain,(
% 7.45/1.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.45/1.52    inference(nnf_transformation,[],[f34])).
% 7.45/1.52  
% 7.45/1.52  fof(f111,plain,(
% 7.45/1.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f71])).
% 7.45/1.52  
% 7.45/1.52  fof(f13,axiom,(
% 7.45/1.52    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f29,plain,(
% 7.45/1.52    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0)),
% 7.45/1.52    inference(pure_predicate_removal,[],[f13])).
% 7.45/1.52  
% 7.45/1.52  fof(f72,plain,(
% 7.45/1.52    ! [X0] : v4_relat_1(k1_xboole_0,X0)),
% 7.45/1.52    inference(rectify,[],[f29])).
% 7.45/1.52  
% 7.45/1.52  fof(f114,plain,(
% 7.45/1.52    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 7.45/1.52    inference(cnf_transformation,[],[f72])).
% 7.45/1.52  
% 7.45/1.52  fof(f7,axiom,(
% 7.45/1.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f68,plain,(
% 7.45/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.45/1.52    inference(nnf_transformation,[],[f7])).
% 7.45/1.52  
% 7.45/1.52  fof(f69,plain,(
% 7.45/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.45/1.52    inference(flattening,[],[f68])).
% 7.45/1.52  
% 7.45/1.52  fof(f106,plain,(
% 7.45/1.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.45/1.52    inference(cnf_transformation,[],[f69])).
% 7.45/1.52  
% 7.45/1.52  fof(f154,plain,(
% 7.45/1.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.45/1.52    inference(equality_resolution,[],[f106])).
% 7.45/1.52  
% 7.45/1.52  fof(f12,axiom,(
% 7.45/1.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.45/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.52  
% 7.45/1.52  fof(f113,plain,(
% 7.45/1.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.45/1.52    inference(cnf_transformation,[],[f12])).
% 7.45/1.52  
% 7.45/1.52  cnf(c_37,plain,
% 7.45/1.52      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.45/1.52      | v5_pre_topc(X0,X1,X2)
% 7.45/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.45/1.52      | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 7.45/1.52      | ~ v1_funct_1(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X2)
% 7.45/1.52      | k2_struct_0(X2) = k1_xboole_0 ),
% 7.45/1.52      inference(cnf_transformation,[],[f127]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_52,negated_conjecture,
% 7.45/1.52      ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
% 7.45/1.52      inference(cnf_transformation,[],[f149]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1322,plain,
% 7.45/1.52      ( v5_pre_topc(X0,X1,X2)
% 7.45/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.45/1.52      | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 7.45/1.52      | ~ v1_funct_1(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X2)
% 7.45/1.52      | k2_struct_0(X2) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(X2) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK6)
% 7.45/1.52      | sK8 != X0 ),
% 7.45/1.52      inference(resolution_lifted,[status(thm)],[c_37,c_52]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1323,plain,
% 7.45/1.52      ( v5_pre_topc(sK8,X0,X1)
% 7.45/1.52      | m1_subset_1(sK2(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | ~ v1_funct_1(sK8)
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | k2_struct_0(X1) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(unflattening,[status(thm)],[c_1322]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_53,negated_conjecture,
% 7.45/1.52      ( v1_funct_1(sK8) ),
% 7.45/1.52      inference(cnf_transformation,[],[f148]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1327,plain,
% 7.45/1.52      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | m1_subset_1(sK2(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.52      | v5_pre_topc(sK8,X0,X1)
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | k2_struct_0(X1) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(global_propositional_subsumption,[status(thm)],[c_1323,c_53]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1328,plain,
% 7.45/1.52      ( v5_pre_topc(sK8,X0,X1)
% 7.45/1.52      | m1_subset_1(sK2(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | k2_struct_0(X1) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(renaming,[status(thm)],[c_1327]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5279,plain,
% 7.45/1.52      ( k2_struct_0(X0) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK6)
% 7.45/1.52      | v5_pre_topc(sK8,X1,X0) = iProver_top
% 7.45/1.52      | m1_subset_1(sK2(X1,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | l1_pre_topc(X0) != iProver_top
% 7.45/1.52      | l1_pre_topc(X1) != iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_1328]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_6282,plain,
% 7.45/1.52      ( k2_struct_0(X0) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | v5_pre_topc(sK8,sK6,X0) = iProver_top
% 7.45/1.52      | m1_subset_1(sK2(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | l1_pre_topc(X0) != iProver_top
% 7.45/1.52      | l1_pre_topc(sK6) != iProver_top ),
% 7.45/1.52      inference(equality_resolution,[status(thm)],[c_5279]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_56,negated_conjecture,
% 7.45/1.52      ( l1_pre_topc(sK6) ),
% 7.45/1.52      inference(cnf_transformation,[],[f145]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_61,plain,
% 7.45/1.52      ( l1_pre_topc(sK6) = iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5792,plain,
% 7.45/1.52      ( v5_pre_topc(sK8,sK6,X0)
% 7.45/1.52      | m1_subset_1(sK2(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0)))
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0))))
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(sK6)
% 7.45/1.52      | k2_struct_0(X0) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(instantiation,[status(thm)],[c_1328]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5793,plain,
% 7.45/1.52      ( k2_struct_0(X0) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 7.45/1.52      | v5_pre_topc(sK8,sK6,X0) = iProver_top
% 7.45/1.52      | m1_subset_1(sK2(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | l1_pre_topc(X0) != iProver_top
% 7.45/1.52      | l1_pre_topc(sK6) != iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_5792]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_4189,plain,( X0 = X0 ),theory(equality) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_6243,plain,
% 7.45/1.52      ( u1_struct_0(sK6) = u1_struct_0(sK6) ),
% 7.45/1.52      inference(instantiation,[status(thm)],[c_4189]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_6965,plain,
% 7.45/1.52      ( l1_pre_topc(X0) != iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | m1_subset_1(sK2(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.45/1.52      | v5_pre_topc(sK8,sK6,X0) = iProver_top
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | k2_struct_0(X0) = k1_xboole_0 ),
% 7.45/1.52      inference(global_propositional_subsumption,
% 7.45/1.52                [status(thm)],
% 7.45/1.52                [c_6282,c_61,c_5793,c_6243]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_6966,plain,
% 7.45/1.52      ( k2_struct_0(X0) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | v5_pre_topc(sK8,sK6,X0) = iProver_top
% 7.45/1.52      | m1_subset_1(sK2(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | l1_pre_topc(X0) != iProver_top ),
% 7.45/1.52      inference(renaming,[status(thm)],[c_6965]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_6977,plain,
% 7.45/1.52      ( k2_struct_0(sK7) = k1_xboole_0
% 7.45/1.52      | v5_pre_topc(sK8,sK6,sK7) = iProver_top
% 7.45/1.52      | m1_subset_1(sK2(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 7.45/1.52      | l1_pre_topc(sK7) != iProver_top ),
% 7.45/1.52      inference(equality_resolution,[status(thm)],[c_6966]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_54,negated_conjecture,
% 7.45/1.52      ( l1_pre_topc(sK7) ),
% 7.45/1.52      inference(cnf_transformation,[],[f147]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_63,plain,
% 7.45/1.52      ( l1_pre_topc(sK7) = iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_51,negated_conjecture,
% 7.45/1.52      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
% 7.45/1.52      inference(cnf_transformation,[],[f150]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_66,plain,
% 7.45/1.52      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_50,negated_conjecture,
% 7.45/1.52      ( ~ v5_pre_topc(sK8,sK6,sK7) ),
% 7.45/1.52      inference(cnf_transformation,[],[f151]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_67,plain,
% 7.45/1.52      ( v5_pre_topc(sK8,sK6,sK7) != iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_7414,plain,
% 7.45/1.52      ( k2_struct_0(sK7) = k1_xboole_0
% 7.45/1.52      | m1_subset_1(sK2(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 7.45/1.52      inference(global_propositional_subsumption,
% 7.45/1.52                [status(thm)],
% 7.45/1.52                [c_6977,c_2458,c_6243,c_6575]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_17,plain,
% 7.45/1.52      ( m1_subset_1(X0,X1)
% 7.45/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.45/1.52      | ~ r2_hidden(X0,X2) ),
% 7.45/1.52      inference(cnf_transformation,[],[f110]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5307,plain,
% 7.45/1.52      ( m1_subset_1(X0,X1) = iProver_top
% 7.45/1.52      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.45/1.52      | r2_hidden(X0,X2) != iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_9915,plain,
% 7.45/1.52      ( k2_struct_0(sK7) = k1_xboole_0
% 7.45/1.52      | m1_subset_1(X0,u1_struct_0(sK7)) = iProver_top
% 7.45/1.52      | r2_hidden(X0,sK2(sK6,sK7,sK8)) != iProver_top ),
% 7.45/1.52      inference(superposition,[status(thm)],[c_7414,c_5307]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_58,negated_conjecture,
% 7.45/1.52      ( v2_pre_topc(sK6) ),
% 7.45/1.52      inference(cnf_transformation,[],[f143]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_57,negated_conjecture,
% 7.45/1.52      ( v1_tdlat_3(sK6) ),
% 7.45/1.52      inference(cnf_transformation,[],[f144]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_33,plain,
% 7.45/1.52      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.45/1.52      | v5_pre_topc(X0,X1,X2)
% 7.45/1.52      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0)),X1)
% 7.45/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.45/1.52      | ~ v1_funct_1(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X2)
% 7.45/1.52      | k2_struct_0(X2) = k1_xboole_0 ),
% 7.45/1.52      inference(cnf_transformation,[],[f131]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1466,plain,
% 7.45/1.52      ( v5_pre_topc(X0,X1,X2)
% 7.45/1.52      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0)),X1)
% 7.45/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.45/1.52      | ~ v1_funct_1(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X2)
% 7.45/1.52      | k2_struct_0(X2) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(X2) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK6)
% 7.45/1.52      | sK8 != X0 ),
% 7.45/1.52      inference(resolution_lifted,[status(thm)],[c_33,c_52]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1467,plain,
% 7.45/1.52      ( v5_pre_topc(sK8,X0,X1)
% 7.45/1.52      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK2(X0,X1,sK8)),X0)
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | ~ v1_funct_1(sK8)
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | k2_struct_0(X1) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(unflattening,[status(thm)],[c_1466]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1471,plain,
% 7.45/1.52      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK2(X0,X1,sK8)),X0)
% 7.45/1.52      | v5_pre_topc(sK8,X0,X1)
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | k2_struct_0(X1) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(global_propositional_subsumption,[status(thm)],[c_1467,c_53]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1472,plain,
% 7.45/1.52      ( v5_pre_topc(sK8,X0,X1)
% 7.45/1.52      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK2(X0,X1,sK8)),X0)
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | k2_struct_0(X1) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(renaming,[status(thm)],[c_1471]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_2373,plain,
% 7.45/1.52      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK2(X0,X1,sK8)),X0)
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | k2_struct_0(X1) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6)
% 7.45/1.52      | sK7 != X1
% 7.45/1.52      | sK6 != X0
% 7.45/1.52      | sK8 != sK8 ),
% 7.45/1.52      inference(resolution_lifted,[status(thm)],[c_50,c_1472]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_2374,plain,
% 7.45/1.52      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),sK6)
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 7.45/1.52      | ~ l1_pre_topc(sK7)
% 7.45/1.52      | ~ l1_pre_topc(sK6)
% 7.45/1.52      | k2_struct_0(sK7) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(unflattening,[status(thm)],[c_2373]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_2376,plain,
% 7.45/1.52      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),sK6)
% 7.45/1.52      | k2_struct_0(sK7) = k1_xboole_0
% 7.45/1.52      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(global_propositional_subsumption,
% 7.45/1.52                [status(thm)],
% 7.45/1.52                [c_2374,c_56,c_54,c_51]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_6575,plain,
% 7.45/1.52      ( u1_struct_0(sK7) = u1_struct_0(sK7) ),
% 7.45/1.52      inference(instantiation,[status(thm)],[c_4189]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_46,plain,
% 7.45/1.52      ( v3_pre_topc(X0,X1)
% 7.45/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.52      | ~ v1_tdlat_3(X1)
% 7.45/1.52      | ~ v2_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X1) ),
% 7.45/1.52      inference(cnf_transformation,[],[f137]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5986,plain,
% 7.45/1.52      ( v3_pre_topc(X0,sK6)
% 7.45/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.45/1.52      | ~ v1_tdlat_3(sK6)
% 7.45/1.52      | ~ v2_pre_topc(sK6)
% 7.45/1.52      | ~ l1_pre_topc(sK6) ),
% 7.45/1.52      inference(instantiation,[status(thm)],[c_46]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_6169,plain,
% 7.45/1.52      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK6),X0,X1,X2),sK6)
% 7.45/1.52      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK6),X0,X1,X2),k1_zfmisc_1(u1_struct_0(sK6)))
% 7.45/1.52      | ~ v1_tdlat_3(sK6)
% 7.45/1.52      | ~ v2_pre_topc(sK6)
% 7.45/1.52      | ~ l1_pre_topc(sK6) ),
% 7.45/1.52      inference(instantiation,[status(thm)],[c_5986]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_6734,plain,
% 7.45/1.52      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),sK6)
% 7.45/1.52      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 7.45/1.52      | ~ v1_tdlat_3(sK6)
% 7.45/1.52      | ~ v2_pre_topc(sK6)
% 7.45/1.52      | ~ l1_pre_topc(sK6) ),
% 7.45/1.52      inference(instantiation,[status(thm)],[c_6169]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_8571,plain,
% 7.45/1.52      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),sK6)
% 7.45/1.52      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
% 7.45/1.52      | ~ v1_tdlat_3(sK6)
% 7.45/1.52      | ~ v2_pre_topc(sK6)
% 7.45/1.52      | ~ l1_pre_topc(sK6) ),
% 7.45/1.52      inference(instantiation,[status(thm)],[c_6734]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_23,plain,
% 7.45/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.52      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 7.45/1.52      inference(cnf_transformation,[],[f116]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5995,plain,
% 7.45/1.52      ( m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
% 7.45/1.52      inference(instantiation,[status(thm)],[c_23]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_9469,plain,
% 7.45/1.52      ( m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
% 7.45/1.52      inference(instantiation,[status(thm)],[c_5995]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_10557,plain,
% 7.45/1.52      ( k2_struct_0(sK7) = k1_xboole_0 ),
% 7.45/1.52      inference(global_propositional_subsumption,
% 7.45/1.52                [status(thm)],
% 7.45/1.52                [c_9915,c_58,c_57,c_56,c_51,c_2376,c_6243,c_6575,c_8571,c_9469]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_27,plain,
% 7.45/1.52      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.45/1.52      inference(cnf_transformation,[],[f120]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_29,plain,
% 7.45/1.52      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 7.45/1.52      inference(cnf_transformation,[],[f122]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_28,plain,
% 7.45/1.52      ( ~ v2_struct_0(X0) | ~ l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0)) ),
% 7.45/1.52      inference(cnf_transformation,[],[f121]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_740,plain,
% 7.45/1.52      ( ~ l1_struct_0(X0)
% 7.45/1.52      | ~ v1_xboole_0(k2_struct_0(X0))
% 7.45/1.52      | v1_xboole_0(u1_struct_0(X0)) ),
% 7.45/1.52      inference(resolution,[status(thm)],[c_29,c_28]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_758,plain,
% 7.45/1.52      ( ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ v1_xboole_0(k2_struct_0(X0))
% 7.45/1.52      | v1_xboole_0(u1_struct_0(X0)) ),
% 7.45/1.52      inference(resolution,[status(thm)],[c_27,c_740]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5288,plain,
% 7.45/1.52      ( l1_pre_topc(X0) != iProver_top
% 7.45/1.52      | v1_xboole_0(k2_struct_0(X0)) != iProver_top
% 7.45/1.52      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_10563,plain,
% 7.45/1.52      ( l1_pre_topc(sK7) != iProver_top
% 7.45/1.52      | v1_xboole_0(u1_struct_0(sK7)) = iProver_top
% 7.45/1.52      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.45/1.52      inference(superposition,[status(thm)],[c_10557,c_5288]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5,plain,
% 7.45/1.52      ( v1_xboole_0(k1_xboole_0) ),
% 7.45/1.52      inference(cnf_transformation,[],[f98]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_185,plain,
% 7.45/1.52      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_11478,plain,
% 7.45/1.52      ( v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
% 7.45/1.52      inference(global_propositional_subsumption,
% 7.45/1.52                [status(thm)],
% 7.45/1.52                [c_10563,c_63,c_185]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5294,plain,
% 7.45/1.52      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_22,plain,
% 7.45/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.52      | ~ v1_xboole_0(X2)
% 7.45/1.52      | v1_xboole_0(X0) ),
% 7.45/1.52      inference(cnf_transformation,[],[f115]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5305,plain,
% 7.45/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.45/1.52      | v1_xboole_0(X2) != iProver_top
% 7.45/1.52      | v1_xboole_0(X0) = iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_9751,plain,
% 7.45/1.52      ( v1_xboole_0(u1_struct_0(sK7)) != iProver_top
% 7.45/1.52      | v1_xboole_0(sK8) = iProver_top ),
% 7.45/1.52      inference(superposition,[status(thm)],[c_5294,c_5305]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_11485,plain,
% 7.45/1.52      ( v1_xboole_0(sK8) = iProver_top ),
% 7.45/1.52      inference(superposition,[status(thm)],[c_11478,c_9751]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_6,plain,
% 7.45/1.52      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.45/1.52      inference(cnf_transformation,[],[f99]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5314,plain,
% 7.45/1.52      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_11579,plain,
% 7.45/1.52      ( sK8 = k1_xboole_0 ),
% 7.45/1.52      inference(superposition,[status(thm)],[c_11485,c_5314]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_0,plain,
% 7.45/1.52      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.45/1.52      inference(cnf_transformation,[],[f94]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5320,plain,
% 7.45/1.52      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_41,plain,
% 7.45/1.52      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.45/1.52      | v5_pre_topc(X0,X1,X2)
% 7.45/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.45/1.52      | m1_subset_1(sK3(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 7.45/1.52      | ~ v1_funct_1(X0)
% 7.45/1.52      | ~ v2_pre_topc(X1)
% 7.45/1.52      | ~ v2_pre_topc(X2)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X2) ),
% 7.45/1.52      inference(cnf_transformation,[],[f134]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1160,plain,
% 7.45/1.52      ( v5_pre_topc(X0,X1,X2)
% 7.45/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.45/1.52      | m1_subset_1(sK3(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 7.45/1.52      | ~ v1_funct_1(X0)
% 7.45/1.52      | ~ v2_pre_topc(X1)
% 7.45/1.52      | ~ v2_pre_topc(X2)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X2)
% 7.45/1.52      | u1_struct_0(X2) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK6)
% 7.45/1.52      | sK8 != X0 ),
% 7.45/1.52      inference(resolution_lifted,[status(thm)],[c_41,c_52]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1161,plain,
% 7.45/1.52      ( v5_pre_topc(sK8,X0,X1)
% 7.45/1.52      | m1_subset_1(sK3(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | ~ v1_funct_1(sK8)
% 7.45/1.52      | ~ v2_pre_topc(X0)
% 7.45/1.52      | ~ v2_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(unflattening,[status(thm)],[c_1160]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1165,plain,
% 7.45/1.52      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | m1_subset_1(sK3(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.52      | v5_pre_topc(sK8,X0,X1)
% 7.45/1.52      | ~ v2_pre_topc(X0)
% 7.45/1.52      | ~ v2_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(global_propositional_subsumption,[status(thm)],[c_1161,c_53]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1166,plain,
% 7.45/1.52      ( v5_pre_topc(sK8,X0,X1)
% 7.45/1.52      | m1_subset_1(sK3(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | ~ v2_pre_topc(X0)
% 7.45/1.52      | ~ v2_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(renaming,[status(thm)],[c_1165]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5283,plain,
% 7.45/1.52      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK6)
% 7.45/1.52      | v5_pre_topc(sK8,X1,X0) = iProver_top
% 7.45/1.52      | m1_subset_1(sK3(X1,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | v2_pre_topc(X0) != iProver_top
% 7.45/1.52      | v2_pre_topc(X1) != iProver_top
% 7.45/1.52      | l1_pre_topc(X0) != iProver_top
% 7.45/1.52      | l1_pre_topc(X1) != iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_1166]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_6590,plain,
% 7.45/1.52      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | v5_pre_topc(sK8,sK6,X0) = iProver_top
% 7.45/1.52      | m1_subset_1(sK3(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | v2_pre_topc(X0) != iProver_top
% 7.45/1.52      | v2_pre_topc(sK6) != iProver_top
% 7.45/1.52      | l1_pre_topc(X0) != iProver_top
% 7.45/1.52      | l1_pre_topc(sK6) != iProver_top ),
% 7.45/1.52      inference(equality_resolution,[status(thm)],[c_5283]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_59,plain,
% 7.45/1.52      ( v2_pre_topc(sK6) = iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5836,plain,
% 7.45/1.52      ( v5_pre_topc(sK8,sK6,X0)
% 7.45/1.52      | m1_subset_1(sK3(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0)))
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0))))
% 7.45/1.52      | ~ v2_pre_topc(X0)
% 7.45/1.52      | ~ v2_pre_topc(sK6)
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(sK6)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(instantiation,[status(thm)],[c_1166]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5837,plain,
% 7.45/1.52      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 7.45/1.52      | v5_pre_topc(sK8,sK6,X0) = iProver_top
% 7.45/1.52      | m1_subset_1(sK3(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | v2_pre_topc(X0) != iProver_top
% 7.45/1.52      | v2_pre_topc(sK6) != iProver_top
% 7.45/1.52      | l1_pre_topc(X0) != iProver_top
% 7.45/1.52      | l1_pre_topc(sK6) != iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_5836]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_7131,plain,
% 7.45/1.52      ( l1_pre_topc(X0) != iProver_top
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | v5_pre_topc(sK8,sK6,X0) = iProver_top
% 7.45/1.52      | m1_subset_1(sK3(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | v2_pre_topc(X0) != iProver_top ),
% 7.45/1.52      inference(global_propositional_subsumption,
% 7.45/1.52                [status(thm)],
% 7.45/1.52                [c_6590,c_59,c_61,c_5837,c_6243]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_7132,plain,
% 7.45/1.52      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | v5_pre_topc(sK8,sK6,X0) = iProver_top
% 7.45/1.52      | m1_subset_1(sK3(sK6,X0,sK8),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | v2_pre_topc(X0) != iProver_top
% 7.45/1.52      | l1_pre_topc(X0) != iProver_top ),
% 7.45/1.52      inference(renaming,[status(thm)],[c_7131]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_7143,plain,
% 7.45/1.52      ( v5_pre_topc(sK8,sK6,sK7) = iProver_top
% 7.45/1.52      | m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 7.45/1.52      | v2_pre_topc(sK7) != iProver_top
% 7.45/1.52      | l1_pre_topc(sK7) != iProver_top ),
% 7.45/1.52      inference(equality_resolution,[status(thm)],[c_7132]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_2490,plain,
% 7.45/1.52      ( m1_subset_1(sK3(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | ~ v2_pre_topc(X0)
% 7.45/1.52      | ~ v2_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6)
% 7.45/1.52      | sK7 != X1
% 7.45/1.52      | sK6 != X0
% 7.45/1.52      | sK8 != sK8 ),
% 7.45/1.52      inference(resolution_lifted,[status(thm)],[c_50,c_1166]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_2491,plain,
% 7.45/1.52      ( m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7)))
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 7.45/1.52      | ~ v2_pre_topc(sK7)
% 7.45/1.52      | ~ v2_pre_topc(sK6)
% 7.45/1.52      | ~ l1_pre_topc(sK7)
% 7.45/1.52      | ~ l1_pre_topc(sK6)
% 7.45/1.52      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(unflattening,[status(thm)],[c_2490]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_55,negated_conjecture,
% 7.45/1.52      ( v2_pre_topc(sK7) ),
% 7.45/1.52      inference(cnf_transformation,[],[f146]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_2493,plain,
% 7.45/1.52      ( m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7)))
% 7.45/1.52      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(global_propositional_subsumption,
% 7.45/1.52                [status(thm)],
% 7.45/1.52                [c_2491,c_58,c_56,c_55,c_54,c_51]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_2495,plain,
% 7.45/1.52      ( u1_struct_0(sK7) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 7.45/1.52      | m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_2493]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_7492,plain,
% 7.45/1.52      ( m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 7.45/1.52      inference(global_propositional_subsumption,
% 7.45/1.52                [status(thm)],
% 7.45/1.52                [c_7143,c_2495,c_6243,c_6575]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_16,plain,
% 7.45/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.45/1.52      inference(cnf_transformation,[],[f108]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5308,plain,
% 7.45/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.45/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_7497,plain,
% 7.45/1.52      ( r1_tarski(sK3(sK6,sK7,sK8),u1_struct_0(sK7)) = iProver_top ),
% 7.45/1.52      inference(superposition,[status(thm)],[c_7492,c_5308]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_4,plain,
% 7.45/1.52      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.45/1.52      inference(cnf_transformation,[],[f95]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5316,plain,
% 7.45/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.45/1.52      | r2_hidden(X2,X0) != iProver_top
% 7.45/1.52      | r2_hidden(X2,X1) = iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_8027,plain,
% 7.45/1.52      ( r2_hidden(X0,sK3(sK6,sK7,sK8)) != iProver_top
% 7.45/1.52      | r2_hidden(X0,u1_struct_0(sK7)) = iProver_top ),
% 7.45/1.52      inference(superposition,[status(thm)],[c_7497,c_5316]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_8594,plain,
% 7.45/1.52      ( r2_hidden(sK0(sK3(sK6,sK7,sK8)),u1_struct_0(sK7)) = iProver_top
% 7.45/1.52      | v1_xboole_0(sK3(sK6,sK7,sK8)) = iProver_top ),
% 7.45/1.52      inference(superposition,[status(thm)],[c_5320,c_8027]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_11600,plain,
% 7.45/1.52      ( r2_hidden(sK0(sK3(sK6,sK7,k1_xboole_0)),u1_struct_0(sK7)) = iProver_top
% 7.45/1.52      | v1_xboole_0(sK3(sK6,sK7,k1_xboole_0)) = iProver_top ),
% 7.45/1.52      inference(demodulation,[status(thm)],[c_11579,c_8594]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1,plain,
% 7.45/1.52      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.45/1.52      inference(cnf_transformation,[],[f93]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5319,plain,
% 7.45/1.52      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_18204,plain,
% 7.45/1.52      ( v1_xboole_0(sK3(sK6,sK7,k1_xboole_0)) = iProver_top
% 7.45/1.52      | v1_xboole_0(u1_struct_0(sK7)) != iProver_top ),
% 7.45/1.52      inference(superposition,[status(thm)],[c_11600,c_5319]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_18624,plain,
% 7.45/1.52      ( v1_xboole_0(sK3(sK6,sK7,k1_xboole_0)) = iProver_top ),
% 7.45/1.52      inference(global_propositional_subsumption,
% 7.45/1.52                [status(thm)],
% 7.45/1.52                [c_18204,c_63,c_185,c_10563]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_18629,plain,
% 7.45/1.52      ( sK3(sK6,sK7,k1_xboole_0) = k1_xboole_0 ),
% 7.45/1.52      inference(superposition,[status(thm)],[c_18624,c_5314]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_11483,plain,
% 7.45/1.52      ( u1_struct_0(sK7) = k1_xboole_0 ),
% 7.45/1.52      inference(superposition,[status(thm)],[c_11478,c_5314]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_40,plain,
% 7.45/1.52      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.45/1.52      | v5_pre_topc(X0,X1,X2)
% 7.45/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.45/1.52      | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK3(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK3(X1,X2,X0))))
% 7.45/1.52      | ~ v1_funct_1(X0)
% 7.45/1.52      | ~ v2_pre_topc(X1)
% 7.45/1.52      | ~ v2_pre_topc(X2)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X2) ),
% 7.45/1.52      inference(cnf_transformation,[],[f135]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1199,plain,
% 7.45/1.52      ( v5_pre_topc(X0,X1,X2)
% 7.45/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.45/1.52      | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK3(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK3(X1,X2,X0))))
% 7.45/1.52      | ~ v1_funct_1(X0)
% 7.45/1.52      | ~ v2_pre_topc(X1)
% 7.45/1.52      | ~ v2_pre_topc(X2)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X2)
% 7.45/1.52      | u1_struct_0(X2) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK6)
% 7.45/1.52      | sK8 != X0 ),
% 7.45/1.52      inference(resolution_lifted,[status(thm)],[c_40,c_52]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1200,plain,
% 7.45/1.52      ( v5_pre_topc(sK8,X0,X1)
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK3(X0,X1,sK8))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,k2_pre_topc(X1,sK3(X0,X1,sK8))))
% 7.45/1.52      | ~ v1_funct_1(sK8)
% 7.45/1.52      | ~ v2_pre_topc(X0)
% 7.45/1.52      | ~ v2_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(unflattening,[status(thm)],[c_1199]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1204,plain,
% 7.45/1.52      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK3(X0,X1,sK8))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,k2_pre_topc(X1,sK3(X0,X1,sK8))))
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | v5_pre_topc(sK8,X0,X1)
% 7.45/1.52      | ~ v2_pre_topc(X0)
% 7.45/1.52      | ~ v2_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(global_propositional_subsumption,[status(thm)],[c_1200,c_53]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_1205,plain,
% 7.45/1.52      ( v5_pre_topc(sK8,X0,X1)
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK3(X0,X1,sK8))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,k2_pre_topc(X1,sK3(X0,X1,sK8))))
% 7.45/1.52      | ~ v2_pre_topc(X0)
% 7.45/1.52      | ~ v2_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(renaming,[status(thm)],[c_1204]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5282,plain,
% 7.45/1.52      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK6)
% 7.45/1.52      | v5_pre_topc(sK8,X1,X0) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK8,sK3(X1,X0,sK8))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK8,k2_pre_topc(X0,sK3(X1,X0,sK8)))) != iProver_top
% 7.45/1.52      | v2_pre_topc(X0) != iProver_top
% 7.45/1.52      | v2_pre_topc(X1) != iProver_top
% 7.45/1.52      | l1_pre_topc(X0) != iProver_top
% 7.45/1.52      | l1_pre_topc(X1) != iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_1205]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_6090,plain,
% 7.45/1.52      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | v5_pre_topc(sK8,sK6,X0) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,sK3(sK6,X0,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,k2_pre_topc(X0,sK3(sK6,X0,sK8)))) != iProver_top
% 7.45/1.52      | v2_pre_topc(X0) != iProver_top
% 7.45/1.52      | v2_pre_topc(sK6) != iProver_top
% 7.45/1.52      | l1_pre_topc(X0) != iProver_top
% 7.45/1.52      | l1_pre_topc(sK6) != iProver_top ),
% 7.45/1.52      inference(equality_resolution,[status(thm)],[c_5282]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5896,plain,
% 7.45/1.52      ( v5_pre_topc(sK8,sK6,X0)
% 7.45/1.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0))))
% 7.45/1.52      | ~ r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,sK3(sK6,X0,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,k2_pre_topc(X0,sK3(sK6,X0,sK8))))
% 7.45/1.52      | ~ v2_pre_topc(X0)
% 7.45/1.52      | ~ v2_pre_topc(sK6)
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(sK6)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(instantiation,[status(thm)],[c_1205]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_5897,plain,
% 7.45/1.52      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 7.45/1.52      | v5_pre_topc(sK8,sK6,X0) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,sK3(sK6,X0,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,k2_pre_topc(X0,sK3(sK6,X0,sK8)))) != iProver_top
% 7.45/1.52      | v2_pre_topc(X0) != iProver_top
% 7.45/1.52      | v2_pre_topc(sK6) != iProver_top
% 7.45/1.52      | l1_pre_topc(X0) != iProver_top
% 7.45/1.52      | l1_pre_topc(sK6) != iProver_top ),
% 7.45/1.52      inference(predicate_to_equality,[status(thm)],[c_5896]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_6794,plain,
% 7.45/1.52      ( l1_pre_topc(X0) != iProver_top
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | v5_pre_topc(sK8,sK6,X0) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,sK3(sK6,X0,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,k2_pre_topc(X0,sK3(sK6,X0,sK8)))) != iProver_top
% 7.45/1.52      | v2_pre_topc(X0) != iProver_top ),
% 7.45/1.52      inference(global_propositional_subsumption,
% 7.45/1.52                [status(thm)],
% 7.45/1.52                [c_6090,c_59,c_61,c_5897,c_6243]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_6795,plain,
% 7.45/1.52      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 7.45/1.52      | v5_pre_topc(sK8,sK6,X0) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 7.45/1.52      | r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,sK3(sK6,X0,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(X0),sK8,k2_pre_topc(X0,sK3(sK6,X0,sK8)))) != iProver_top
% 7.45/1.52      | v2_pre_topc(X0) != iProver_top
% 7.45/1.52      | l1_pre_topc(X0) != iProver_top ),
% 7.45/1.52      inference(renaming,[status(thm)],[c_6794]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_6806,plain,
% 7.45/1.52      ( v5_pre_topc(sK8,sK6,sK7) = iProver_top
% 7.45/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 7.45/1.52      | r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK3(sK6,sK7,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,k2_pre_topc(sK7,sK3(sK6,sK7,sK8)))) != iProver_top
% 7.45/1.52      | v2_pre_topc(sK7) != iProver_top
% 7.45/1.52      | l1_pre_topc(sK7) != iProver_top ),
% 7.45/1.52      inference(equality_resolution,[status(thm)],[c_6795]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_2473,plain,
% 7.45/1.52      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.45/1.52      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,sK3(X0,X1,sK8))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK8,k2_pre_topc(X1,sK3(X0,X1,sK8))))
% 7.45/1.52      | ~ v2_pre_topc(X0)
% 7.45/1.52      | ~ v2_pre_topc(X1)
% 7.45/1.52      | ~ l1_pre_topc(X0)
% 7.45/1.52      | ~ l1_pre_topc(X1)
% 7.45/1.52      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(X0) != u1_struct_0(sK6)
% 7.45/1.52      | sK7 != X1
% 7.45/1.52      | sK6 != X0
% 7.45/1.52      | sK8 != sK8 ),
% 7.45/1.52      inference(resolution_lifted,[status(thm)],[c_50,c_1205]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_2474,plain,
% 7.45/1.52      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 7.45/1.52      | ~ r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK3(sK6,sK7,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,k2_pre_topc(sK7,sK3(sK6,sK7,sK8))))
% 7.45/1.52      | ~ v2_pre_topc(sK7)
% 7.45/1.52      | ~ v2_pre_topc(sK6)
% 7.45/1.52      | ~ l1_pre_topc(sK7)
% 7.45/1.52      | ~ l1_pre_topc(sK6)
% 7.45/1.52      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 7.45/1.52      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 7.45/1.52      inference(unflattening,[status(thm)],[c_2473]) ).
% 7.45/1.52  
% 7.45/1.52  cnf(c_2476,plain,
% 7.45/1.52      ( ~ r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK3(sK6,sK7,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,k2_pre_topc(sK7,sK3(sK6,sK7,sK8))))
% 7.45/1.53      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 7.45/1.53      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 7.45/1.53      inference(global_propositional_subsumption,
% 7.45/1.53                [status(thm)],
% 7.45/1.53                [c_2474,c_58,c_56,c_55,c_54,c_51]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_2478,plain,
% 7.45/1.53      ( u1_struct_0(sK7) != u1_struct_0(sK7)
% 7.45/1.53      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 7.45/1.53      | r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK3(sK6,sK7,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,k2_pre_topc(sK7,sK3(sK6,sK7,sK8)))) != iProver_top ),
% 7.45/1.53      inference(predicate_to_equality,[status(thm)],[c_2476]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_7181,plain,
% 7.45/1.53      ( r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK3(sK6,sK7,sK8))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,k2_pre_topc(sK7,sK3(sK6,sK7,sK8)))) != iProver_top ),
% 7.45/1.53      inference(global_propositional_subsumption,
% 7.45/1.53                [status(thm)],
% 7.45/1.53                [c_6806,c_2478,c_6243,c_6575]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_11617,plain,
% 7.45/1.53      ( r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,sK3(sK6,sK7,k1_xboole_0))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,k2_pre_topc(sK7,sK3(sK6,sK7,k1_xboole_0)))) != iProver_top ),
% 7.45/1.53      inference(demodulation,[status(thm)],[c_11579,c_7181]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_19140,plain,
% 7.45/1.53      ( r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,sK3(sK6,sK7,k1_xboole_0))),k8_relset_1(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK7,sK3(sK6,sK7,k1_xboole_0)))) != iProver_top ),
% 7.45/1.53      inference(demodulation,[status(thm)],[c_11483,c_11617]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_24363,plain,
% 7.45/1.53      ( r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK7,k1_xboole_0))) != iProver_top ),
% 7.45/1.53      inference(demodulation,[status(thm)],[c_18629,c_19140]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_25,plain,
% 7.45/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.53      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 7.45/1.53      inference(cnf_transformation,[],[f119]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_5302,plain,
% 7.45/1.53      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 7.45/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.45/1.53      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_8798,plain,
% 7.45/1.53      ( k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,u1_struct_0(sK7)) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8) ),
% 7.45/1.53      inference(superposition,[status(thm)],[c_5294,c_5302]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_24,plain,
% 7.45/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.45/1.53      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.45/1.53      inference(cnf_transformation,[],[f117]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_5303,plain,
% 7.45/1.53      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.45/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.45/1.53      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_7701,plain,
% 7.45/1.53      ( k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8) = k1_relat_1(sK8) ),
% 7.45/1.53      inference(superposition,[status(thm)],[c_5294,c_5303]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_8810,plain,
% 7.45/1.53      ( k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,u1_struct_0(sK7)) = k1_relat_1(sK8) ),
% 7.45/1.53      inference(light_normalisation,[status(thm)],[c_8798,c_7701]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_5304,plain,
% 7.45/1.53      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.45/1.53      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 7.45/1.53      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_9537,plain,
% 7.45/1.53      ( m1_subset_1(k1_relat_1(sK8),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.45/1.53      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top ),
% 7.45/1.53      inference(superposition,[status(thm)],[c_8810,c_5304]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_10185,plain,
% 7.45/1.53      ( m1_subset_1(k1_relat_1(sK8),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.45/1.53      inference(global_propositional_subsumption,[status(thm)],[c_9537,c_66]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_49,plain,
% 7.45/1.53      ( v4_pre_topc(X0,X1)
% 7.45/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.53      | ~ v1_tdlat_3(X1)
% 7.45/1.53      | ~ v2_pre_topc(X1)
% 7.45/1.53      | ~ l1_pre_topc(X1) ),
% 7.45/1.53      inference(cnf_transformation,[],[f140]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_31,plain,
% 7.45/1.53      ( ~ v4_pre_topc(X0,X1)
% 7.45/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.53      | ~ l1_pre_topc(X1)
% 7.45/1.53      | k2_pre_topc(X1,X0) = X0 ),
% 7.45/1.53      inference(cnf_transformation,[],[f123]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_805,plain,
% 7.45/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.53      | ~ v1_tdlat_3(X1)
% 7.45/1.53      | ~ v2_pre_topc(X1)
% 7.45/1.53      | ~ l1_pre_topc(X1)
% 7.45/1.53      | k2_pre_topc(X1,X0) = X0 ),
% 7.45/1.53      inference(resolution,[status(thm)],[c_49,c_31]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_43,plain,
% 7.45/1.53      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 7.45/1.53      inference(cnf_transformation,[],[f136]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_819,plain,
% 7.45/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.53      | ~ v1_tdlat_3(X1)
% 7.45/1.53      | ~ l1_pre_topc(X1)
% 7.45/1.53      | k2_pre_topc(X1,X0) = X0 ),
% 7.45/1.53      inference(forward_subsumption_resolution,[status(thm)],[c_805,c_43]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_5286,plain,
% 7.45/1.53      ( k2_pre_topc(X0,X1) = X1
% 7.45/1.53      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.45/1.53      | v1_tdlat_3(X0) != iProver_top
% 7.45/1.53      | l1_pre_topc(X0) != iProver_top ),
% 7.45/1.53      inference(predicate_to_equality,[status(thm)],[c_819]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_10192,plain,
% 7.45/1.53      ( k2_pre_topc(sK6,k1_relat_1(sK8)) = k1_relat_1(sK8)
% 7.45/1.53      | v1_tdlat_3(sK6) != iProver_top
% 7.45/1.53      | l1_pre_topc(sK6) != iProver_top ),
% 7.45/1.53      inference(superposition,[status(thm)],[c_10185,c_5286]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_60,plain,
% 7.45/1.53      ( v1_tdlat_3(sK6) = iProver_top ),
% 7.45/1.53      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_10476,plain,
% 7.45/1.53      ( k2_pre_topc(sK6,k1_relat_1(sK8)) = k1_relat_1(sK8) ),
% 7.45/1.53      inference(global_propositional_subsumption,
% 7.45/1.53                [status(thm)],
% 7.45/1.53                [c_10192,c_60,c_61]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_11592,plain,
% 7.45/1.53      ( k2_pre_topc(sK6,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 7.45/1.53      inference(demodulation,[status(thm)],[c_11579,c_10476]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_11601,plain,
% 7.45/1.53      ( k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,u1_struct_0(sK7)) = k1_relat_1(k1_xboole_0) ),
% 7.45/1.53      inference(demodulation,[status(thm)],[c_11579,c_8810]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_19161,plain,
% 7.45/1.53      ( k8_relset_1(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 7.45/1.53      inference(demodulation,[status(thm)],[c_11483,c_11601]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_24384,plain,
% 7.45/1.53      ( r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(u1_struct_0(sK6),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK7,k1_xboole_0))) != iProver_top ),
% 7.45/1.53      inference(light_normalisation,[status(thm)],[c_24363,c_11592,c_19161]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_3,plain,
% 7.45/1.53      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.45/1.53      inference(cnf_transformation,[],[f96]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_5317,plain,
% 7.45/1.53      ( r1_tarski(X0,X1) = iProver_top
% 7.45/1.53      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 7.45/1.53      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_10190,plain,
% 7.45/1.53      ( r1_tarski(k1_relat_1(sK8),u1_struct_0(sK6)) = iProver_top ),
% 7.45/1.53      inference(superposition,[status(thm)],[c_10185,c_5308]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_10353,plain,
% 7.45/1.53      ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
% 7.45/1.53      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 7.45/1.53      inference(superposition,[status(thm)],[c_10190,c_5316]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_11589,plain,
% 7.45/1.53      ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
% 7.45/1.53      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 7.45/1.53      inference(demodulation,[status(thm)],[c_11579,c_10353]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_16325,plain,
% 7.45/1.53      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
% 7.45/1.53      | r2_hidden(sK1(k1_relat_1(k1_xboole_0),X0),u1_struct_0(sK6)) = iProver_top ),
% 7.45/1.53      inference(superposition,[status(thm)],[c_5317,c_11589]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_19,plain,
% 7.45/1.53      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.45/1.53      inference(cnf_transformation,[],[f111]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_21,plain,
% 7.45/1.53      ( v4_relat_1(k1_xboole_0,X0) ),
% 7.45/1.53      inference(cnf_transformation,[],[f114]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_777,plain,
% 7.45/1.53      ( r1_tarski(k1_relat_1(X0),X1)
% 7.45/1.53      | ~ v1_relat_1(X0)
% 7.45/1.53      | X2 != X1
% 7.45/1.53      | k1_xboole_0 != X0 ),
% 7.45/1.53      inference(resolution_lifted,[status(thm)],[c_19,c_21]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_778,plain,
% 7.45/1.53      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~ v1_relat_1(k1_xboole_0) ),
% 7.45/1.53      inference(unflattening,[status(thm)],[c_777]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_779,plain,
% 7.45/1.53      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
% 7.45/1.53      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.45/1.53      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_11,plain,
% 7.45/1.53      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.45/1.53      inference(cnf_transformation,[],[f154]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_20,plain,
% 7.45/1.53      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.45/1.53      inference(cnf_transformation,[],[f113]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_5306,plain,
% 7.45/1.53      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.45/1.53      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_6418,plain,
% 7.45/1.53      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.45/1.53      inference(superposition,[status(thm)],[c_11,c_5306]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_19043,plain,
% 7.45/1.53      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 7.45/1.53      inference(global_propositional_subsumption,
% 7.45/1.53                [status(thm)],
% 7.45/1.53                [c_16325,c_779,c_6418]) ).
% 7.45/1.53  
% 7.45/1.53  cnf(c_24586,plain,
% 7.45/1.53      ( $false ),
% 7.45/1.53      inference(forward_subsumption_resolution,[status(thm)],[c_24384,c_19043]) ).
% 7.45/1.53  
% 7.45/1.53  
% 7.45/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.45/1.53  
% 7.45/1.53  ------                               Statistics
% 7.45/1.53  
% 7.45/1.53  ------ General
% 7.45/1.53  
% 7.45/1.53  abstr_ref_over_cycles:                  0
% 7.45/1.53  abstr_ref_under_cycles:                 0
% 7.45/1.53  gc_basic_clause_elim:                   0
% 7.45/1.53  forced_gc_time:                         0
% 7.45/1.53  parsing_time:                           0.011
% 7.45/1.53  unif_index_cands_time:                  0.
% 7.45/1.53  unif_index_add_time:                    0.
% 7.45/1.53  orderings_time:                         0.
% 7.45/1.53  out_proof_time:                         0.022
% 7.45/1.53  total_time:                             0.703
% 7.45/1.53  num_of_symbols:                         67
% 7.45/1.53  num_of_terms:                           16290
% 7.45/1.53  
% 7.45/1.53  ------ Preprocessing
% 7.45/1.53  
% 7.45/1.53  num_of_splits:                          0
% 7.45/1.53  num_of_split_atoms:                     0
% 7.45/1.53  num_of_reused_defs:                     0
% 7.45/1.53  num_eq_ax_congr_red:                    77
% 7.45/1.53  num_of_sem_filtered_clauses:            1
% 7.45/1.53  num_of_subtypes:                        0
% 7.45/1.53  monotx_restored_types:                  0
% 7.45/1.53  sat_num_of_epr_types:                   0
% 7.45/1.53  sat_num_of_non_cyclic_types:            0
% 7.45/1.53  sat_guarded_non_collapsed_types:        0
% 7.45/1.53  num_pure_diseq_elim:                    0
% 7.45/1.53  simp_replaced_by:                       0
% 7.45/1.53  res_preprocessed:                       249
% 7.45/1.53  prep_upred:                             0
% 7.45/1.53  prep_unflattend:                        73
% 7.45/1.53  smt_new_axioms:                         0
% 7.45/1.53  pred_elim_cands:                        10
% 7.45/1.53  pred_elim:                              6
% 7.45/1.53  pred_elim_cl:                           8
% 7.45/1.53  pred_elim_cycles:                       13
% 7.45/1.53  merged_defs:                            8
% 7.45/1.53  merged_defs_ncl:                        0
% 7.45/1.53  bin_hyper_res:                          8
% 7.45/1.53  prep_cycles:                            4
% 7.45/1.53  pred_elim_time:                         0.101
% 7.45/1.53  splitting_time:                         0.
% 7.45/1.53  sem_filter_time:                        0.
% 7.45/1.53  monotx_time:                            0.
% 7.45/1.53  subtype_inf_time:                       0.
% 7.45/1.53  
% 7.45/1.53  ------ Problem properties
% 7.45/1.53  
% 7.45/1.53  clauses:                                50
% 7.45/1.53  conjectures:                            7
% 7.45/1.53  epr:                                    14
% 7.45/1.53  horn:                                   38
% 7.45/1.53  ground:                                 8
% 7.45/1.53  unary:                                  14
% 7.45/1.53  binary:                                 12
% 7.45/1.53  lits:                                   180
% 7.45/1.53  lits_eq:                                42
% 7.45/1.53  fd_pure:                                0
% 7.45/1.53  fd_pseudo:                              0
% 7.45/1.53  fd_cond:                                2
% 7.45/1.53  fd_pseudo_cond:                         1
% 7.45/1.53  ac_symbols:                             0
% 7.45/1.53  
% 7.45/1.53  ------ Propositional Solver
% 7.45/1.53  
% 7.45/1.53  prop_solver_calls:                      29
% 7.45/1.53  prop_fast_solver_calls:                 4146
% 7.45/1.53  smt_solver_calls:                       0
% 7.45/1.53  smt_fast_solver_calls:                  0
% 7.45/1.53  prop_num_of_clauses:                    7638
% 7.45/1.53  prop_preprocess_simplified:             17355
% 7.45/1.53  prop_fo_subsumed:                       175
% 7.45/1.53  prop_solver_time:                       0.
% 7.45/1.53  smt_solver_time:                        0.
% 7.45/1.53  smt_fast_solver_time:                   0.
% 7.45/1.53  prop_fast_solver_time:                  0.
% 7.45/1.53  prop_unsat_core_time:                   0.
% 7.45/1.53  
% 7.45/1.53  ------ QBF
% 7.45/1.53  
% 7.45/1.53  qbf_q_res:                              0
% 7.45/1.53  qbf_num_tautologies:                    0
% 7.45/1.53  qbf_prep_cycles:                        0
% 7.45/1.53  
% 7.45/1.53  ------ BMC1
% 7.45/1.53  
% 7.45/1.53  bmc1_current_bound:                     -1
% 7.45/1.53  bmc1_last_solved_bound:                 -1
% 7.45/1.53  bmc1_unsat_core_size:                   -1
% 7.45/1.53  bmc1_unsat_core_parents_size:           -1
% 7.45/1.53  bmc1_merge_next_fun:                    0
% 7.45/1.53  bmc1_unsat_core_clauses_time:           0.
% 7.45/1.53  
% 7.45/1.53  ------ Instantiation
% 7.45/1.53  
% 7.45/1.53  inst_num_of_clauses:                    2207
% 7.45/1.53  inst_num_in_passive:                    150
% 7.45/1.53  inst_num_in_active:                     1020
% 7.45/1.53  inst_num_in_unprocessed:                1040
% 7.45/1.53  inst_num_of_loops:                      1430
% 7.45/1.53  inst_num_of_learning_restarts:          0
% 7.45/1.53  inst_num_moves_active_passive:          407
% 7.45/1.53  inst_lit_activity:                      0
% 7.45/1.53  inst_lit_activity_moves:                0
% 7.45/1.53  inst_num_tautologies:                   0
% 7.45/1.53  inst_num_prop_implied:                  0
% 7.45/1.53  inst_num_existing_simplified:           0
% 7.45/1.53  inst_num_eq_res_simplified:             0
% 7.45/1.53  inst_num_child_elim:                    0
% 7.45/1.53  inst_num_of_dismatching_blockings:      927
% 7.45/1.53  inst_num_of_non_proper_insts:           2404
% 7.45/1.53  inst_num_of_duplicates:                 0
% 7.45/1.53  inst_inst_num_from_inst_to_res:         0
% 7.45/1.53  inst_dismatching_checking_time:         0.
% 7.45/1.53  
% 7.45/1.53  ------ Resolution
% 7.45/1.53  
% 7.45/1.53  res_num_of_clauses:                     0
% 7.45/1.53  res_num_in_passive:                     0
% 7.45/1.53  res_num_in_active:                      0
% 7.45/1.53  res_num_of_loops:                       253
% 7.45/1.53  res_forward_subset_subsumed:            118
% 7.45/1.53  res_backward_subset_subsumed:           14
% 7.45/1.53  res_forward_subsumed:                   9
% 7.45/1.53  res_backward_subsumed:                  0
% 7.45/1.53  res_forward_subsumption_resolution:     1
% 7.45/1.53  res_backward_subsumption_resolution:    0
% 7.45/1.53  res_clause_to_clause_subsumption:       3240
% 7.45/1.53  res_orphan_elimination:                 0
% 7.45/1.53  res_tautology_del:                      122
% 7.45/1.53  res_num_eq_res_simplified:              0
% 7.45/1.53  res_num_sel_changes:                    0
% 7.45/1.53  res_moves_from_active_to_pass:          0
% 7.45/1.53  
% 7.45/1.53  ------ Superposition
% 7.45/1.53  
% 7.45/1.53  sup_time_total:                         0.
% 7.45/1.53  sup_time_generating:                    0.
% 7.45/1.53  sup_time_sim_full:                      0.
% 7.45/1.53  sup_time_sim_immed:                     0.
% 7.45/1.53  
% 7.45/1.53  sup_num_of_clauses:                     464
% 7.45/1.53  sup_num_in_active:                      169
% 7.45/1.53  sup_num_in_passive:                     295
% 7.45/1.53  sup_num_of_loops:                       284
% 7.45/1.53  sup_fw_superposition:                   364
% 7.45/1.53  sup_bw_superposition:                   159
% 7.45/1.53  sup_immediate_simplified:               168
% 7.45/1.53  sup_given_eliminated:                   3
% 7.45/1.53  comparisons_done:                       0
% 7.45/1.53  comparisons_avoided:                    6
% 7.45/1.53  
% 7.45/1.53  ------ Simplifications
% 7.45/1.53  
% 7.45/1.53  
% 7.45/1.53  sim_fw_subset_subsumed:                 40
% 7.45/1.53  sim_bw_subset_subsumed:                 26
% 7.45/1.53  sim_fw_subsumed:                        14
% 7.45/1.53  sim_bw_subsumed:                        0
% 7.45/1.53  sim_fw_subsumption_res:                 13
% 7.45/1.53  sim_bw_subsumption_res:                 0
% 7.45/1.53  sim_tautology_del:                      11
% 7.45/1.53  sim_eq_tautology_del:                   8
% 7.45/1.53  sim_eq_res_simp:                        8
% 7.45/1.53  sim_fw_demodulated:                     77
% 7.45/1.53  sim_bw_demodulated:                     108
% 7.45/1.53  sim_light_normalised:                   44
% 7.45/1.53  sim_joinable_taut:                      0
% 7.45/1.53  sim_joinable_simp:                      0
% 7.45/1.53  sim_ac_normalised:                      0
% 7.45/1.53  sim_smt_subsumption:                    0
% 7.45/1.53  
%------------------------------------------------------------------------------
