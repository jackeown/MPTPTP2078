%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:46 EST 2020

% Result     : Theorem 23.35s
% Output     : CNFRefutation 23.35s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_5787)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X2] :
                    ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                    | ~ r2_hidden(X2,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X2] :
                    ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                    | ~ r2_hidden(X2,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,u1_struct_0(X1))
                     => k1_funct_1(X2,X3) = X3 ) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
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
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,u1_struct_0(X1))
                       => k1_funct_1(X2,X3) = X3 ) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
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
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
          & ! [X3] :
              ( k1_funct_1(X2,X3) = X3
              | ~ r2_hidden(X3,u1_struct_0(X1))
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK4)
        & ! [X3] :
            ( k1_funct_1(sK4,X3) = X3
            | ~ r2_hidden(X3,u1_struct_0(X1))
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k4_tmap_1(X0,sK3),X2)
            & ! [X3] :
                ( k1_funct_1(X2,X3) = X3
                | ~ r2_hidden(X3,u1_struct_0(sK3))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
                & ! [X3] :
                    ( k1_funct_1(X2,X3) = X3
                    | ~ r2_hidden(X3,u1_struct_0(X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK2),k4_tmap_1(sK2,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4)
    & ! [X3] :
        ( k1_funct_1(sK4,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f47,f46,f45])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f80,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
        & m1_subset_1(sK0(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
                & m1_subset_1(sK0(X0,X2,X3),X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,(
    ! [X3] :
      ( k1_funct_1(sK4,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
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

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1775,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1773,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1779,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3609,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),sK4) = u1_struct_0(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_1779])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1785,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2431,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1773,c_1785])).

cnf(c_3621,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK4)
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3609,c_2431])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3626,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3621])).

cnf(c_3856,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK4)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3621,c_29,c_3626])).

cnf(c_3857,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK4) ),
    inference(renaming,[status(thm)],[c_3856])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_455,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_34])).

cnf(c_456,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_460,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_35,c_33])).

cnf(c_510,plain,
    ( m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_460])).

cnf(c_511,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_1769,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_3865,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK4)
    | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3857,c_1769])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1783,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4217,plain,
    ( k4_tmap_1(sK2,sK3) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK4)
    | u1_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3865,c_1783])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_437,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_438,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_funct_1(k4_tmap_1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_442,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v1_funct_1(k4_tmap_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_35,c_33])).

cnf(c_517,plain,
    ( v1_funct_1(k4_tmap_1(sK2,X0))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_442])).

cnf(c_518,plain,
    ( v1_funct_1(k4_tmap_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_22,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_392,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_393,plain,
    ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_397,plain,
    ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_35,c_33])).

cnf(c_545,plain,
    ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_397])).

cnf(c_546,plain,
    ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_14,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_830,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k4_tmap_1(sK2,sK3) != X0
    | k1_funct_1(X3,sK0(X1,X0,X3)) != k1_funct_1(X0,sK0(X1,X0,X3))
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK3) != X1
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_831,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_830])).

cnf(c_1256,plain,
    ( X0 != X1
    | X2 != X3
    | k1_funct_1(X0,X2) = k1_funct_1(X1,X3) ),
    theory(equality)).

cnf(c_2122,plain,
    ( sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) != sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4))
    | sK4 != k4_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_1246,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2250,plain,
    ( k4_tmap_1(sK2,sK3) != X0
    | sK4 != X0
    | sK4 = k4_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_2251,plain,
    ( k4_tmap_1(sK2,sK3) != k1_xboole_0
    | sK4 = k4_tmap_1(sK2,sK3)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2250])).

cnf(c_1766,plain,
    ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_3867,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK4)
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3857,c_1766])).

cnf(c_3942,plain,
    ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),k1_xboole_0)
    | u1_struct_0(sK3) = k1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3867])).

cnf(c_4245,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),k1_xboole_0)
    | k4_tmap_1(sK2,sK3) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK4)
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4217])).

cnf(c_3869,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3857,c_1773])).

cnf(c_4035,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK4)
    | u1_struct_0(sK3) = k1_xboole_0
    | sK4 = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3869,c_1783])).

cnf(c_1772,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3870,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK4)
    | v1_funct_2(sK4,u1_struct_0(sK3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3857,c_1772])).

cnf(c_4475,plain,
    ( sK4 = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4035,c_3870])).

cnf(c_4476,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK4)
    | u1_struct_0(sK3) = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4475])).

cnf(c_1245,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5589,plain,
    ( sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) = sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_5647,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(sK3) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4217,c_30,c_29,c_28,c_511,c_518,c_546,c_831,c_2122,c_2251,c_3942,c_4245,c_4476,c_5589])).

cnf(c_5648,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK4)
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5647])).

cnf(c_3610,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1769,c_1779])).

cnf(c_2533,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(k4_tmap_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_1769,c_1785])).

cnf(c_3614,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3610,c_2533])).

cnf(c_3625,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3614])).

cnf(c_7698,plain,
    ( k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3614,c_546,c_3625])).

cnf(c_7699,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_7698])).

cnf(c_18,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1777,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7703,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK3)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7699,c_1777])).

cnf(c_512,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_519,plain,
    ( v1_funct_1(k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2052,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2223,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v1_relat_1(k4_tmap_1(sK2,sK3))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_2052])).

cnf(c_2224,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2223])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2298,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2299,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2298])).

cnf(c_10451,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK3)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7703,c_512,c_519,c_2224,c_2299])).

cnf(c_10452,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK3)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10451])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_488,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_489,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_503,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_489])).

cnf(c_504,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_1770,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1788,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2914,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1770,c_1788])).

cnf(c_10466,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10452,c_2914])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k1_funct_1(sK4,X0) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1774,plain,
    ( k1_funct_1(sK4,X0) = X0
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10468,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10452,c_1774])).

cnf(c_10505,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10466,c_10468])).

cnf(c_10786,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7699,c_10505])).

cnf(c_10858,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5648,c_10786])).

cnf(c_19807,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1775,c_10858])).

cnf(c_41,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2220,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2052])).

cnf(c_2221,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2220])).

cnf(c_19948,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19807,c_41,c_43,c_2221,c_2299])).

cnf(c_19949,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_19948])).

cnf(c_7705,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7699,c_1775])).

cnf(c_7907,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7705,c_512,c_519,c_2224,c_2299])).

cnf(c_7908,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7907])).

cnf(c_19976,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19949,c_7908])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_116,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_120,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2184,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_2414,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_2444,plain,
    ( k4_tmap_1(sK2,sK3) = k4_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_2512,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK2)
    | u1_struct_0(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_2513,plain,
    ( u1_struct_0(sK2) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2512])).

cnf(c_2481,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_3064,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2481])).

cnf(c_3065,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_3064])).

cnf(c_2658,plain,
    ( X0 != X1
    | k4_tmap_1(sK2,sK3) != X1
    | k4_tmap_1(sK2,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_3681,plain,
    ( X0 != k4_tmap_1(sK2,sK3)
    | k4_tmap_1(sK2,sK3) = X0
    | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2658])).

cnf(c_3682,plain,
    ( k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
    | k4_tmap_1(sK2,sK3) = k1_xboole_0
    | k1_xboole_0 != k4_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3681])).

cnf(c_1254,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_2130,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | X2 != u1_struct_0(sK2)
    | X1 != u1_struct_0(sK3)
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_2312,plain,
    ( v1_funct_2(sK4,X0,X1)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | X1 != u1_struct_0(sK2)
    | X0 != u1_struct_0(sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2130])).

cnf(c_4100,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),X0)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | X0 != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2312])).

cnf(c_4102,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | v1_funct_2(sK4,u1_struct_0(sK3),k1_xboole_0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != sK4
    | k1_xboole_0 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4100])).

cnf(c_1252,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_3001,plain,
    ( X0 != u1_struct_0(sK2)
    | X1 != u1_struct_0(sK3)
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1252])).

cnf(c_4971,plain,
    ( X0 != u1_struct_0(sK2)
    | k2_zfmisc_1(u1_struct_0(sK3),X0) = k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3001])).

cnf(c_4972,plain,
    ( k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0) = k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | k1_xboole_0 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4971])).

cnf(c_2135,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | X0 != k4_tmap_1(sK2,sK3)
    | X2 != u1_struct_0(sK2)
    | X1 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_4142,plain,
    ( v1_funct_2(X0,u1_struct_0(sK3),X1)
    | ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | X0 != k4_tmap_1(sK2,sK3)
    | X1 != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2135])).

cnf(c_5899,plain,
    ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),X0)
    | ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | X0 != u1_struct_0(sK2)
    | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4142])).

cnf(c_5901,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),k1_xboole_0)
    | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | k1_xboole_0 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5899])).

cnf(c_3009,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6153,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),k1_xboole_0)
    | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)))
    | k1_xboole_0 = k4_tmap_1(sK2,sK3)
    | k1_xboole_0 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3009])).

cnf(c_3286,plain,
    ( X0 != X1
    | u1_struct_0(sK3) != X1
    | u1_struct_0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_6808,plain,
    ( X0 != u1_struct_0(sK3)
    | u1_struct_0(sK3) = X0
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3286])).

cnf(c_6809,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_6808])).

cnf(c_8566,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),k1_xboole_0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)))
    | k1_xboole_0 = u1_struct_0(sK3)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_3009])).

cnf(c_1250,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2362,plain,
    ( X0 != k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1250])).

cnf(c_3000,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_2362])).

cnf(c_11493,plain,
    ( k2_zfmisc_1(u1_struct_0(sK3),X0) != k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3000])).

cnf(c_11494,plain,
    ( k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0) != k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_11493])).

cnf(c_1248,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2112,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | X0 != k4_tmap_1(sK2,sK3)
    | X1 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1248])).

cnf(c_2443,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),X0)
    | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | X0 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
    | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2112])).

cnf(c_43162,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0)))
    | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_2443])).

cnf(c_43165,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)))
    | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_43162])).

cnf(c_2102,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | X1 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1248])).

cnf(c_2183,plain,
    ( m1_subset_1(sK4,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | X0 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2102])).

cnf(c_2361,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2183])).

cnf(c_43177,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2361])).

cnf(c_43179,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_43177])).

cnf(c_54629,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19976,c_30,c_29,c_28,c_116,c_120,c_511,c_518,c_546,c_831,c_2122,c_2184,c_2251,c_2414,c_2444,c_2513,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,c_11494,c_43165,c_43179])).

cnf(c_1791,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_54648,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | u1_struct_0(sK3) = k1_xboole_0
    | k1_relat_1(X0) = u1_struct_0(sK3)
    | r1_tarski(k1_relat_1(X0),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_54629,c_1791])).

cnf(c_2608,plain,
    ( k4_tmap_1(sK2,sK3) != sK4
    | sK4 = k4_tmap_1(sK2,sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2250])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1790,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7918,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(u1_struct_0(sK3),k1_relat_1(k4_tmap_1(sK2,sK3))) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1790,c_7908])).

cnf(c_8229,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(u1_struct_0(sK3),k1_relat_1(k4_tmap_1(sK2,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7918,c_512,c_519,c_2224,c_2299])).

cnf(c_8235,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5648,c_8229])).

cnf(c_5661,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5648,c_2914])).

cnf(c_5672,plain,
    ( k1_funct_1(sK4,X0) = X0
    | u1_struct_0(sK3) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5648,c_1774])).

cnf(c_5739,plain,
    ( k1_funct_1(sK4,X0) = X0
    | u1_struct_0(sK3) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5661,c_5672])).

cnf(c_6758,plain,
    ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_5739])).

cnf(c_9003,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6758,c_41,c_43,c_2221,c_2299])).

cnf(c_9004,plain,
    ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9003])).

cnf(c_14233,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8235,c_9004])).

cnf(c_9017,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7699,c_9004])).

cnf(c_14224,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7699,c_8235])).

cnf(c_19603,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14233,c_512,c_519,c_2224,c_2299,c_9017,c_14224])).

cnf(c_7707,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
    | r1_tarski(k1_relat_1(X0),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7699,c_1775])).

cnf(c_8731,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
    | r1_tarski(k1_relat_1(X0),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7707,c_512,c_519,c_2224,c_2299])).

cnf(c_8732,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
    | r1_tarski(k1_relat_1(X0),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8731])).

cnf(c_8742,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1790,c_8732])).

cnf(c_8840,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8742,c_512,c_519,c_2224,c_2299])).

cnf(c_8847,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5648,c_8840])).

cnf(c_17338,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8847,c_10505])).

cnf(c_17647,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17338,c_41,c_43,c_2221,c_2299])).

cnf(c_17657,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17647,c_1791])).

cnf(c_18059,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17657,c_30,c_29,c_28,c_511,c_518,c_546,c_831,c_2122,c_2184,c_2608,c_5589])).

cnf(c_19621,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19603,c_18059])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_tarski(X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1776,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4258,plain,
    ( k1_funct_1(X0,sK1(X1,X2)) = k1_funct_1(X1,sK1(X1,X2))
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k1_relat_1(X1),k1_relat_1(X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_1776])).

cnf(c_10310,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(X1,sK1(k4_tmap_1(sK2,sK3),X0))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7699,c_4258])).

cnf(c_15012,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(X1,sK1(k4_tmap_1(sK2,sK3),X0))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10310,c_512,c_519,c_2224,c_2299])).

cnf(c_15013,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(X1,sK1(k4_tmap_1(sK2,sK3),X0))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_15012])).

cnf(c_17665,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_17647,c_15013])).

cnf(c_17,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2609,plain,
    ( r1_tarski(X0,k4_tmap_1(sK2,sK3))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(k4_tmap_1(sK2,sK3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k4_tmap_1(sK2,sK3))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(X0,k4_tmap_1(sK2,sK3))) != k1_funct_1(X0,sK1(X0,k4_tmap_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3754,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3))
    | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(k4_tmap_1(sK2,sK3))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) != k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_2609])).

cnf(c_3755,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) != k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3754])).

cnf(c_5663,plain,
    ( k1_relset_1(k1_relat_1(sK4),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5648,c_2533])).

cnf(c_5665,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5648,c_1769])).

cnf(c_6521,plain,
    ( k1_relset_1(k1_relat_1(sK4),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(k4_tmap_1(sK2,sK3),k1_relat_1(sK4),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5665,c_1779])).

cnf(c_5669,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(k4_tmap_1(sK2,sK3),k1_relat_1(sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5648,c_1766])).

cnf(c_7211,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relset_1(k1_relat_1(sK4),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6521,c_5787,c_6550])).

cnf(c_7212,plain,
    ( k1_relset_1(k1_relat_1(sK4),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7211])).

cnf(c_8543,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_5663,c_7212])).

cnf(c_16043,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8543,c_1776])).

cnf(c_16878,plain,
    ( v1_relat_1(X1) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16043,c_512,c_519,c_2224,c_2299])).

cnf(c_16879,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_16878])).

cnf(c_17664,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_17647,c_16879])).

cnf(c_20329,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17664,c_41,c_43,c_2221,c_2299])).

cnf(c_20340,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_20329])).

cnf(c_21563,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20340,c_41,c_43,c_2221,c_2299])).

cnf(c_21564,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_21563])).

cnf(c_21579,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8235,c_21564])).

cnf(c_21637,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17665,c_30,c_41,c_29,c_28,c_43,c_511,c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,c_2299,c_2608,c_3755,c_5589,c_8235,c_17657,c_21579])).

cnf(c_53785,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19621,c_30,c_29,c_28,c_116,c_120,c_511,c_518,c_546,c_831,c_2122,c_2184,c_2251,c_2414,c_2444,c_2513,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,c_11494,c_21637,c_43165,c_43179])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_410,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_411,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ r2_hidden(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k1_funct_1(k4_tmap_1(sK2,X0),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_415,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ r2_hidden(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(X0)
    | k1_funct_1(k4_tmap_1(sK2,X0),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_35,c_33])).

cnf(c_524,plain,
    ( ~ r2_hidden(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(X1)
    | k1_funct_1(k4_tmap_1(sK2,X1),X0) = X0
    | sK2 != sK2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_415])).

cnf(c_525,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_529,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_525,c_32])).

cnf(c_530,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
    inference(renaming,[status(thm)],[c_529])).

cnf(c_1767,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_5664,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
    | u1_struct_0(sK3) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5648,c_1767])).

cnf(c_5740,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
    | u1_struct_0(sK3) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5661,c_5664])).

cnf(c_8610,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_5740])).

cnf(c_9526,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8610,c_41,c_43,c_2221,c_2299])).

cnf(c_9527,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9526])).

cnf(c_9540,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7699,c_9527])).

cnf(c_14232,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8235,c_9527])).

cnf(c_20583,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9540,c_512,c_519,c_2224,c_2299,c_14232])).

cnf(c_20584,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_20583])).

cnf(c_10467,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10452,c_1767])).

cnf(c_10506,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10466,c_10467])).

cnf(c_17337,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8847,c_10506])).

cnf(c_18407,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17337,c_41,c_43,c_2221,c_2299])).

cnf(c_18417,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18407,c_1791])).

cnf(c_18555,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18417,c_30,c_29,c_28,c_511,c_518,c_546,c_831,c_2122,c_2184,c_2608,c_5589])).

cnf(c_20601,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20584,c_18555])).

cnf(c_54012,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20601,c_30,c_29,c_28,c_116,c_120,c_511,c_518,c_546,c_831,c_2122,c_2184,c_2251,c_2414,c_2444,c_2513,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,c_11494,c_43165,c_43179])).

cnf(c_54013,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_54012])).

cnf(c_1778,plain,
    ( k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | r1_tarski(X1,X0) = iProver_top
    | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_54017,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_54013,c_1778])).

cnf(c_20593,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_20584,c_1791])).

cnf(c_54162,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_54017,c_30,c_41,c_29,c_28,c_43,c_116,c_120,c_511,c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,c_2251,c_2299,c_2414,c_2444,c_2513,c_2608,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,c_8847,c_11494,c_20593,c_21637,c_43165,c_43179])).

cnf(c_54163,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_54162])).

cnf(c_54166,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_54163,c_30,c_41,c_29,c_28,c_43,c_116,c_120,c_511,c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,c_2251,c_2299,c_2414,c_2444,c_2513,c_2608,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,c_8847,c_11494,c_20593,c_21637,c_43165,c_43179,c_54017])).

cnf(c_54167,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_54166])).

cnf(c_54170,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) != sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_54167,c_1778])).

cnf(c_19620,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19603,c_18555])).

cnf(c_53789,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19620,c_30,c_29,c_28,c_116,c_120,c_511,c_518,c_546,c_831,c_2122,c_2184,c_2251,c_2414,c_2444,c_2513,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,c_11494,c_43165,c_43179])).

cnf(c_53790,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_53789])).

cnf(c_53794,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_53790,c_1778])).

cnf(c_19613,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_19603,c_1791])).

cnf(c_54153,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_53794,c_30,c_41,c_29,c_28,c_43,c_116,c_120,c_511,c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,c_2251,c_2299,c_2414,c_2444,c_2513,c_2608,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,c_8847,c_11494,c_19613,c_21637,c_43165,c_43179])).

cnf(c_54154,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_54153])).

cnf(c_54157,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_54154,c_30,c_41,c_29,c_28,c_43,c_116,c_120,c_511,c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,c_2251,c_2299,c_2414,c_2444,c_2513,c_2608,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,c_8847,c_11494,c_19613,c_21637,c_43165,c_43179,c_53794])).

cnf(c_54158,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_54157])).

cnf(c_54185,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_54170,c_30,c_41,c_29,c_28,c_43,c_116,c_120,c_511,c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,c_2251,c_2299,c_2414,c_2444,c_2513,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8235,c_8566,c_11494,c_43165,c_43179,c_54158])).

cnf(c_54195,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_54185,c_1791])).

cnf(c_18424,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_18407,c_16879])).

cnf(c_58165,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18424,c_30,c_29,c_28,c_116,c_120,c_511,c_518,c_546,c_831,c_2122,c_2184,c_2251,c_2414,c_2444,c_2513,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,c_11494,c_43165,c_43179,c_54215])).

cnf(c_58166,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_58165])).

cnf(c_58169,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_58166,c_1778])).

cnf(c_54641,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | u1_struct_0(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5648,c_54629])).

cnf(c_9091,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(X0))
    | ~ r1_tarski(sK4,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_9096,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9091])).

cnf(c_54821,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_54641,c_41,c_43,c_2221,c_2299,c_9096])).

cnf(c_54837,plain,
    ( k1_relat_1(X0) = k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_54821,c_1791])).

cnf(c_55194,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4)
    | r1_tarski(u1_struct_0(sK3),k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7699,c_54837])).

cnf(c_42,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_547,plain,
    ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_4997,plain,
    ( k1_relat_1(sK4) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_5002,plain,
    ( X0 != X1
    | k1_relat_1(sK4) != X1
    | k1_relat_1(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_10112,plain,
    ( X0 != k1_relat_1(sK4)
    | k1_relat_1(sK4) = X0
    | k1_relat_1(sK4) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5002])).

cnf(c_18634,plain,
    ( u1_struct_0(sK3) != k1_relat_1(sK4)
    | k1_relat_1(sK4) = u1_struct_0(sK3)
    | k1_relat_1(sK4) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10112])).

cnf(c_14575,plain,
    ( X0 != X1
    | k1_relat_1(k4_tmap_1(sK2,sK3)) != X1
    | k1_relat_1(k4_tmap_1(sK2,sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_22509,plain,
    ( X0 != u1_struct_0(sK3)
    | k1_relat_1(k4_tmap_1(sK2,sK3)) = X0
    | k1_relat_1(k4_tmap_1(sK2,sK3)) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_14575])).

cnf(c_34112,plain,
    ( k1_relat_1(k4_tmap_1(sK2,sK3)) != u1_struct_0(sK3)
    | k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4)
    | k1_relat_1(sK4) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_22509])).

cnf(c_55209,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_55194,c_42,c_547,c_3614,c_3621,c_4997,c_18634,c_34112])).

cnf(c_55252,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_55209,c_1775])).

cnf(c_56577,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_55252,c_512,c_519,c_2224,c_2299])).

cnf(c_56578,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_56577])).

cnf(c_56588,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1790,c_56578])).

cnf(c_58172,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_56588,c_512,c_519,c_2224,c_2299])).

cnf(c_58718,plain,
    ( u1_struct_0(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_54648,c_30,c_41,c_29,c_28,c_43,c_116,c_120,c_511,c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,c_2251,c_2299,c_2414,c_2444,c_2513,c_2608,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,c_11494,c_43165,c_43179,c_53785,c_54195,c_58169,c_58172])).

cnf(c_59018,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(k4_tmap_1(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_58718,c_2533])).

cnf(c_59020,plain,
    ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_58718,c_1769])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1780,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_61312,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_xboole_0
    | v1_funct_2(k4_tmap_1(sK2,sK3),k1_xboole_0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_59020,c_1780])).

cnf(c_2419,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK3)
    | u1_struct_0(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_2420,plain,
    ( u1_struct_0(sK3) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2419])).

cnf(c_2507,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_2506,plain,
    ( v1_funct_2(X0,X1,u1_struct_0(sK2))
    | ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | X0 != k4_tmap_1(sK2,sK3)
    | X1 != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2135])).

cnf(c_16677,plain,
    ( v1_funct_2(k4_tmap_1(sK2,sK3),X0,u1_struct_0(sK2))
    | ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | X0 != u1_struct_0(sK3)
    | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2506])).

cnf(c_16678,plain,
    ( X0 != u1_struct_0(sK3)
    | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v1_funct_2(k4_tmap_1(sK2,sK3),X0,u1_struct_0(sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16677])).

cnf(c_16680,plain,
    ( k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | k1_xboole_0 != u1_struct_0(sK3)
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK2,sK3),k1_xboole_0,u1_struct_0(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_16678])).

cnf(c_61401,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_61312,c_30,c_41,c_29,c_28,c_43,c_116,c_120,c_511,c_512,c_518,c_519,c_546,c_547,c_831,c_2122,c_2184,c_2221,c_2224,c_2251,c_2299,c_2414,c_2420,c_2444,c_2507,c_2513,c_2608,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,c_11494,c_16680,c_43165,c_43179,c_53785,c_54195,c_58169,c_58172])).

cnf(c_62400,plain,
    ( k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_59018,c_61401])).

cnf(c_62425,plain,
    ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_xboole_0) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_62400,c_1777])).

cnf(c_62576,plain,
    ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_xboole_0) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_62425,c_62400])).

cnf(c_64099,plain,
    ( v1_relat_1(X0) != iProver_top
    | r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_xboole_0) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_62576,c_512,c_519,c_2224,c_2299])).

cnf(c_64100,plain,
    ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_xboole_0) = iProver_top
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_64099])).

cnf(c_59015,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_58718,c_2914])).

cnf(c_59019,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_58718,c_1767])).

cnf(c_59072,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_59015,c_59019])).

cnf(c_64111,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_64100,c_59072])).

cnf(c_59027,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_58718,c_1773])).

cnf(c_61040,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK2),sK4) = k1_xboole_0
    | v1_funct_2(sK4,k1_xboole_0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_59027,c_1780])).

cnf(c_2945,plain,
    ( v1_funct_2(sK4,X0,u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | X0 != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2312])).

cnf(c_2946,plain,
    ( X0 != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK4 != sK4
    | v1_funct_2(sK4,X0,u1_struct_0(sK2)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2945])).

cnf(c_2948,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK4 != sK4
    | k1_xboole_0 != u1_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK4,k1_xboole_0,u1_struct_0(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2946])).

cnf(c_61341,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK2),sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_61040,c_30,c_41,c_29,c_42,c_28,c_43,c_116,c_120,c_511,c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,c_2251,c_2299,c_2414,c_2420,c_2444,c_2507,c_2513,c_2608,c_2948,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,c_11494,c_43165,c_43179,c_53785,c_54195,c_58169,c_58172])).

cnf(c_59021,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK2),sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_58718,c_2431])).

cnf(c_61344,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_61341,c_59021])).

cnf(c_62085,plain,
    ( r2_hidden(sK1(sK4,X0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_61344,c_1777])).

cnf(c_62236,plain,
    ( r2_hidden(sK1(sK4,X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_62085,c_61344])).

cnf(c_63664,plain,
    ( v1_relat_1(X0) != iProver_top
    | r2_hidden(sK1(sK4,X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_62236,c_41,c_43,c_2221,c_2299])).

cnf(c_63665,plain,
    ( r2_hidden(sK1(sK4,X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_63664])).

cnf(c_63676,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
    | r1_tarski(sK4,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_63665,c_59072])).

cnf(c_64899,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_62400,c_63676])).

cnf(c_115,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_117,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_72229,plain,
    ( r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_64899,c_117,c_512,c_519,c_2224,c_2299])).

cnf(c_72230,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_72229])).

cnf(c_72239,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_72230,c_1791])).

cnf(c_2150,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5499,plain,
    ( ~ r1_tarski(k4_tmap_1(sK2,sK3),sK4)
    | ~ r1_tarski(sK4,k4_tmap_1(sK2,sK3))
    | k4_tmap_1(sK2,sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_2150])).

cnf(c_5500,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5499])).

cnf(c_64978,plain,
    ( k4_tmap_1(sK2,sK3) = X0
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_64111,c_1791])).

cnf(c_72244,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_72230,c_64978])).

cnf(c_72324,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_72244,c_61344])).

cnf(c_72419,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_72324])).

cnf(c_72608,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_72324,c_30,c_41,c_29,c_28,c_43,c_117,c_511,c_518,c_546,c_831,c_2122,c_2184,c_2221,c_2299,c_2608,c_5589])).

cnf(c_72609,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
    inference(renaming,[status(thm)],[c_72608])).

cnf(c_72612,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_72609,c_1778])).

cnf(c_72613,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_72612,c_61344,c_62400])).

cnf(c_59026,plain,
    ( k1_funct_1(sK4,X0) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_58718,c_1774])).

cnf(c_59071,plain,
    ( k1_funct_1(sK4,X0) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_59015,c_59026])).

cnf(c_64112,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_64100,c_59071])).

cnf(c_64281,plain,
    ( k4_tmap_1(sK2,sK3) = X0
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
    | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_64112,c_1791])).

cnf(c_72245,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_72230,c_64281])).

cnf(c_72311,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_72245,c_61344])).

cnf(c_72763,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_72613,c_30,c_41,c_29,c_28,c_43,c_117,c_511,c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,c_2299,c_2608,c_5589,c_72239,c_72311])).

cnf(c_72766,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) != sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) != iProver_top
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_72763,c_1778])).

cnf(c_63677,plain,
    ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
    | r1_tarski(sK4,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_63665,c_59071])).

cnf(c_63856,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_62400,c_63677])).

cnf(c_65420,plain,
    ( r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_63856,c_117,c_512,c_519,c_2224,c_2299])).

cnf(c_65421,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_65420])).

cnf(c_65428,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_65421,c_1791])).

cnf(c_65430,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_65421,c_64281])).

cnf(c_65490,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_65430,c_61344])).

cnf(c_65429,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_65421,c_64978])).

cnf(c_65503,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_65429,c_61344])).

cnf(c_65987,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_65503,c_30,c_41,c_29,c_28,c_43,c_117,c_511,c_518,c_546,c_831,c_2122,c_2184,c_2221,c_2299,c_2608,c_5589])).

cnf(c_65988,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
    inference(renaming,[status(thm)],[c_65987])).

cnf(c_65991,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_65988,c_1778])).

cnf(c_65992,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
    | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_65991,c_61344,c_62400])).

cnf(c_66001,plain,
    ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_65428,c_30,c_41,c_29,c_28,c_43,c_117,c_511,c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,c_2299,c_2608,c_5589,c_65490,c_65992])).

cnf(c_72767,plain,
    ( sK1(sK4,k4_tmap_1(sK2,sK3)) != sK1(sK4,k4_tmap_1(sK2,sK3))
    | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_72766,c_61344,c_62400,c_66001])).

cnf(c_72768,plain,
    ( r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_72767])).

cnf(c_72779,plain,
    ( r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_72239,c_30,c_41,c_29,c_28,c_43,c_117,c_511,c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,c_2299,c_2608,c_5500,c_5589,c_72768])).

cnf(c_72788,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_64111,c_72779])).

cnf(c_72814,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_72788,c_61344])).

cnf(c_73124,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_72814,c_41,c_43,c_117,c_2221,c_2299])).

cnf(c_73201,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_73124,c_1778])).

cnf(c_72789,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_64112,c_72779])).

cnf(c_72805,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_72789,c_61344])).

cnf(c_73012,plain,
    ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_72805,c_41,c_43,c_117,c_2221,c_2299])).

cnf(c_73202,plain,
    ( sK1(k4_tmap_1(sK2,sK3),sK4) != sK1(k4_tmap_1(sK2,sK3),sK4)
    | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_73201,c_61344,c_62400,c_73012])).

cnf(c_73203,plain,
    ( r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_73202])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73203,c_72768,c_5589,c_5500,c_2608,c_2299,c_2224,c_2221,c_2184,c_2122,c_831,c_546,c_519,c_518,c_512,c_511,c_117,c_43,c_28,c_29,c_41,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.35/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.35/3.50  
% 23.35/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.35/3.50  
% 23.35/3.50  ------  iProver source info
% 23.35/3.50  
% 23.35/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.35/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.35/3.50  git: non_committed_changes: false
% 23.35/3.50  git: last_make_outside_of_git: false
% 23.35/3.50  
% 23.35/3.50  ------ 
% 23.35/3.50  
% 23.35/3.50  ------ Input Options
% 23.35/3.50  
% 23.35/3.50  --out_options                           all
% 23.35/3.50  --tptp_safe_out                         true
% 23.35/3.50  --problem_path                          ""
% 23.35/3.50  --include_path                          ""
% 23.35/3.50  --clausifier                            res/vclausify_rel
% 23.35/3.50  --clausifier_options                    --mode clausify
% 23.35/3.50  --stdin                                 false
% 23.35/3.50  --stats_out                             all
% 23.35/3.50  
% 23.35/3.50  ------ General Options
% 23.35/3.50  
% 23.35/3.50  --fof                                   false
% 23.35/3.50  --time_out_real                         305.
% 23.35/3.50  --time_out_virtual                      -1.
% 23.35/3.50  --symbol_type_check                     false
% 23.35/3.50  --clausify_out                          false
% 23.35/3.50  --sig_cnt_out                           false
% 23.35/3.50  --trig_cnt_out                          false
% 23.35/3.50  --trig_cnt_out_tolerance                1.
% 23.35/3.50  --trig_cnt_out_sk_spl                   false
% 23.35/3.50  --abstr_cl_out                          false
% 23.35/3.50  
% 23.35/3.50  ------ Global Options
% 23.35/3.50  
% 23.35/3.50  --schedule                              default
% 23.35/3.50  --add_important_lit                     false
% 23.35/3.50  --prop_solver_per_cl                    1000
% 23.35/3.50  --min_unsat_core                        false
% 23.35/3.50  --soft_assumptions                      false
% 23.35/3.50  --soft_lemma_size                       3
% 23.35/3.50  --prop_impl_unit_size                   0
% 23.35/3.50  --prop_impl_unit                        []
% 23.35/3.50  --share_sel_clauses                     true
% 23.35/3.50  --reset_solvers                         false
% 23.35/3.50  --bc_imp_inh                            [conj_cone]
% 23.35/3.50  --conj_cone_tolerance                   3.
% 23.35/3.50  --extra_neg_conj                        none
% 23.35/3.50  --large_theory_mode                     true
% 23.35/3.50  --prolific_symb_bound                   200
% 23.35/3.50  --lt_threshold                          2000
% 23.35/3.50  --clause_weak_htbl                      true
% 23.35/3.50  --gc_record_bc_elim                     false
% 23.35/3.50  
% 23.35/3.50  ------ Preprocessing Options
% 23.35/3.50  
% 23.35/3.50  --preprocessing_flag                    true
% 23.35/3.50  --time_out_prep_mult                    0.1
% 23.35/3.50  --splitting_mode                        input
% 23.35/3.50  --splitting_grd                         true
% 23.35/3.50  --splitting_cvd                         false
% 23.35/3.50  --splitting_cvd_svl                     false
% 23.35/3.50  --splitting_nvd                         32
% 23.35/3.50  --sub_typing                            true
% 23.35/3.50  --prep_gs_sim                           true
% 23.35/3.50  --prep_unflatten                        true
% 23.35/3.50  --prep_res_sim                          true
% 23.35/3.50  --prep_upred                            true
% 23.35/3.50  --prep_sem_filter                       exhaustive
% 23.35/3.50  --prep_sem_filter_out                   false
% 23.35/3.50  --pred_elim                             true
% 23.35/3.50  --res_sim_input                         true
% 23.35/3.50  --eq_ax_congr_red                       true
% 23.35/3.50  --pure_diseq_elim                       true
% 23.35/3.50  --brand_transform                       false
% 23.35/3.50  --non_eq_to_eq                          false
% 23.35/3.50  --prep_def_merge                        true
% 23.35/3.50  --prep_def_merge_prop_impl              false
% 23.35/3.50  --prep_def_merge_mbd                    true
% 23.35/3.50  --prep_def_merge_tr_red                 false
% 23.35/3.50  --prep_def_merge_tr_cl                  false
% 23.35/3.50  --smt_preprocessing                     true
% 23.35/3.50  --smt_ac_axioms                         fast
% 23.35/3.50  --preprocessed_out                      false
% 23.35/3.50  --preprocessed_stats                    false
% 23.35/3.50  
% 23.35/3.50  ------ Abstraction refinement Options
% 23.35/3.50  
% 23.35/3.50  --abstr_ref                             []
% 23.35/3.50  --abstr_ref_prep                        false
% 23.35/3.50  --abstr_ref_until_sat                   false
% 23.35/3.50  --abstr_ref_sig_restrict                funpre
% 23.35/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.35/3.50  --abstr_ref_under                       []
% 23.35/3.50  
% 23.35/3.50  ------ SAT Options
% 23.35/3.50  
% 23.35/3.50  --sat_mode                              false
% 23.35/3.50  --sat_fm_restart_options                ""
% 23.35/3.50  --sat_gr_def                            false
% 23.35/3.50  --sat_epr_types                         true
% 23.35/3.50  --sat_non_cyclic_types                  false
% 23.35/3.50  --sat_finite_models                     false
% 23.35/3.50  --sat_fm_lemmas                         false
% 23.35/3.50  --sat_fm_prep                           false
% 23.35/3.50  --sat_fm_uc_incr                        true
% 23.35/3.50  --sat_out_model                         small
% 23.35/3.50  --sat_out_clauses                       false
% 23.35/3.50  
% 23.35/3.50  ------ QBF Options
% 23.35/3.50  
% 23.35/3.50  --qbf_mode                              false
% 23.35/3.50  --qbf_elim_univ                         false
% 23.35/3.50  --qbf_dom_inst                          none
% 23.35/3.50  --qbf_dom_pre_inst                      false
% 23.35/3.50  --qbf_sk_in                             false
% 23.35/3.50  --qbf_pred_elim                         true
% 23.35/3.50  --qbf_split                             512
% 23.35/3.50  
% 23.35/3.50  ------ BMC1 Options
% 23.35/3.50  
% 23.35/3.50  --bmc1_incremental                      false
% 23.35/3.50  --bmc1_axioms                           reachable_all
% 23.35/3.50  --bmc1_min_bound                        0
% 23.35/3.50  --bmc1_max_bound                        -1
% 23.35/3.50  --bmc1_max_bound_default                -1
% 23.35/3.50  --bmc1_symbol_reachability              true
% 23.35/3.50  --bmc1_property_lemmas                  false
% 23.35/3.50  --bmc1_k_induction                      false
% 23.35/3.50  --bmc1_non_equiv_states                 false
% 23.35/3.50  --bmc1_deadlock                         false
% 23.35/3.50  --bmc1_ucm                              false
% 23.35/3.50  --bmc1_add_unsat_core                   none
% 23.35/3.50  --bmc1_unsat_core_children              false
% 23.35/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.35/3.50  --bmc1_out_stat                         full
% 23.35/3.50  --bmc1_ground_init                      false
% 23.35/3.50  --bmc1_pre_inst_next_state              false
% 23.35/3.50  --bmc1_pre_inst_state                   false
% 23.35/3.50  --bmc1_pre_inst_reach_state             false
% 23.35/3.50  --bmc1_out_unsat_core                   false
% 23.35/3.50  --bmc1_aig_witness_out                  false
% 23.35/3.50  --bmc1_verbose                          false
% 23.35/3.50  --bmc1_dump_clauses_tptp                false
% 23.35/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.35/3.50  --bmc1_dump_file                        -
% 23.35/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.35/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.35/3.50  --bmc1_ucm_extend_mode                  1
% 23.35/3.50  --bmc1_ucm_init_mode                    2
% 23.35/3.50  --bmc1_ucm_cone_mode                    none
% 23.35/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.35/3.50  --bmc1_ucm_relax_model                  4
% 23.35/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.35/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.35/3.50  --bmc1_ucm_layered_model                none
% 23.35/3.50  --bmc1_ucm_max_lemma_size               10
% 23.35/3.50  
% 23.35/3.50  ------ AIG Options
% 23.35/3.50  
% 23.35/3.50  --aig_mode                              false
% 23.35/3.50  
% 23.35/3.50  ------ Instantiation Options
% 23.35/3.50  
% 23.35/3.50  --instantiation_flag                    true
% 23.35/3.50  --inst_sos_flag                         false
% 23.35/3.50  --inst_sos_phase                        true
% 23.35/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.35/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.35/3.50  --inst_lit_sel_side                     num_symb
% 23.35/3.50  --inst_solver_per_active                1400
% 23.35/3.50  --inst_solver_calls_frac                1.
% 23.35/3.50  --inst_passive_queue_type               priority_queues
% 23.35/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.35/3.50  --inst_passive_queues_freq              [25;2]
% 23.35/3.50  --inst_dismatching                      true
% 23.35/3.50  --inst_eager_unprocessed_to_passive     true
% 23.35/3.50  --inst_prop_sim_given                   true
% 23.35/3.50  --inst_prop_sim_new                     false
% 23.35/3.50  --inst_subs_new                         false
% 23.35/3.50  --inst_eq_res_simp                      false
% 23.35/3.50  --inst_subs_given                       false
% 23.35/3.50  --inst_orphan_elimination               true
% 23.35/3.50  --inst_learning_loop_flag               true
% 23.35/3.50  --inst_learning_start                   3000
% 23.35/3.50  --inst_learning_factor                  2
% 23.35/3.50  --inst_start_prop_sim_after_learn       3
% 23.35/3.50  --inst_sel_renew                        solver
% 23.35/3.50  --inst_lit_activity_flag                true
% 23.35/3.50  --inst_restr_to_given                   false
% 23.35/3.50  --inst_activity_threshold               500
% 23.35/3.50  --inst_out_proof                        true
% 23.35/3.50  
% 23.35/3.50  ------ Resolution Options
% 23.35/3.50  
% 23.35/3.50  --resolution_flag                       true
% 23.35/3.50  --res_lit_sel                           adaptive
% 23.35/3.50  --res_lit_sel_side                      none
% 23.35/3.50  --res_ordering                          kbo
% 23.35/3.50  --res_to_prop_solver                    active
% 23.35/3.50  --res_prop_simpl_new                    false
% 23.35/3.50  --res_prop_simpl_given                  true
% 23.35/3.50  --res_passive_queue_type                priority_queues
% 23.35/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.35/3.50  --res_passive_queues_freq               [15;5]
% 23.35/3.50  --res_forward_subs                      full
% 23.35/3.50  --res_backward_subs                     full
% 23.35/3.50  --res_forward_subs_resolution           true
% 23.35/3.50  --res_backward_subs_resolution          true
% 23.35/3.50  --res_orphan_elimination                true
% 23.35/3.50  --res_time_limit                        2.
% 23.35/3.50  --res_out_proof                         true
% 23.35/3.50  
% 23.35/3.50  ------ Superposition Options
% 23.35/3.50  
% 23.35/3.50  --superposition_flag                    true
% 23.35/3.50  --sup_passive_queue_type                priority_queues
% 23.35/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.35/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.35/3.50  --demod_completeness_check              fast
% 23.35/3.50  --demod_use_ground                      true
% 23.35/3.50  --sup_to_prop_solver                    passive
% 23.35/3.50  --sup_prop_simpl_new                    true
% 23.35/3.50  --sup_prop_simpl_given                  true
% 23.35/3.50  --sup_fun_splitting                     false
% 23.35/3.50  --sup_smt_interval                      50000
% 23.35/3.50  
% 23.35/3.50  ------ Superposition Simplification Setup
% 23.35/3.50  
% 23.35/3.50  --sup_indices_passive                   []
% 23.35/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.35/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.35/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.35/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.35/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.35/3.50  --sup_full_bw                           [BwDemod]
% 23.35/3.50  --sup_immed_triv                        [TrivRules]
% 23.35/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.35/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.35/3.50  --sup_immed_bw_main                     []
% 23.35/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.35/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.35/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.35/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.35/3.50  
% 23.35/3.50  ------ Combination Options
% 23.35/3.50  
% 23.35/3.50  --comb_res_mult                         3
% 23.35/3.50  --comb_sup_mult                         2
% 23.35/3.50  --comb_inst_mult                        10
% 23.35/3.50  
% 23.35/3.50  ------ Debug Options
% 23.35/3.50  
% 23.35/3.50  --dbg_backtrace                         false
% 23.35/3.50  --dbg_dump_prop_clauses                 false
% 23.35/3.50  --dbg_dump_prop_clauses_file            -
% 23.35/3.50  --dbg_out_stat                          false
% 23.35/3.50  ------ Parsing...
% 23.35/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.35/3.50  
% 23.35/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 23.35/3.50  
% 23.35/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.35/3.50  
% 23.35/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.35/3.50  ------ Proving...
% 23.35/3.50  ------ Problem Properties 
% 23.35/3.50  
% 23.35/3.50  
% 23.35/3.50  clauses                                 30
% 23.35/3.50  conjectures                             4
% 23.35/3.50  EPR                                     4
% 23.35/3.50  Horn                                    24
% 23.35/3.50  unary                                   11
% 23.35/3.50  binary                                  2
% 23.35/3.50  lits                                    96
% 23.35/3.50  lits eq                                 19
% 23.35/3.50  fd_pure                                 0
% 23.35/3.50  fd_pseudo                               0
% 23.35/3.50  fd_cond                                 3
% 23.35/3.50  fd_pseudo_cond                          1
% 23.35/3.50  AC symbols                              0
% 23.35/3.50  
% 23.35/3.50  ------ Schedule dynamic 5 is on 
% 23.35/3.50  
% 23.35/3.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.35/3.50  
% 23.35/3.50  
% 23.35/3.50  ------ 
% 23.35/3.50  Current options:
% 23.35/3.50  ------ 
% 23.35/3.50  
% 23.35/3.50  ------ Input Options
% 23.35/3.50  
% 23.35/3.50  --out_options                           all
% 23.35/3.50  --tptp_safe_out                         true
% 23.35/3.50  --problem_path                          ""
% 23.35/3.50  --include_path                          ""
% 23.35/3.50  --clausifier                            res/vclausify_rel
% 23.35/3.50  --clausifier_options                    --mode clausify
% 23.35/3.50  --stdin                                 false
% 23.35/3.50  --stats_out                             all
% 23.35/3.50  
% 23.35/3.50  ------ General Options
% 23.35/3.50  
% 23.35/3.50  --fof                                   false
% 23.35/3.50  --time_out_real                         305.
% 23.35/3.50  --time_out_virtual                      -1.
% 23.35/3.50  --symbol_type_check                     false
% 23.35/3.50  --clausify_out                          false
% 23.35/3.50  --sig_cnt_out                           false
% 23.35/3.50  --trig_cnt_out                          false
% 23.35/3.50  --trig_cnt_out_tolerance                1.
% 23.35/3.50  --trig_cnt_out_sk_spl                   false
% 23.35/3.50  --abstr_cl_out                          false
% 23.35/3.50  
% 23.35/3.50  ------ Global Options
% 23.35/3.50  
% 23.35/3.50  --schedule                              default
% 23.35/3.50  --add_important_lit                     false
% 23.35/3.50  --prop_solver_per_cl                    1000
% 23.35/3.50  --min_unsat_core                        false
% 23.35/3.50  --soft_assumptions                      false
% 23.35/3.50  --soft_lemma_size                       3
% 23.35/3.50  --prop_impl_unit_size                   0
% 23.35/3.50  --prop_impl_unit                        []
% 23.35/3.50  --share_sel_clauses                     true
% 23.35/3.50  --reset_solvers                         false
% 23.35/3.50  --bc_imp_inh                            [conj_cone]
% 23.35/3.50  --conj_cone_tolerance                   3.
% 23.35/3.50  --extra_neg_conj                        none
% 23.35/3.50  --large_theory_mode                     true
% 23.35/3.50  --prolific_symb_bound                   200
% 23.35/3.50  --lt_threshold                          2000
% 23.35/3.50  --clause_weak_htbl                      true
% 23.35/3.50  --gc_record_bc_elim                     false
% 23.35/3.50  
% 23.35/3.50  ------ Preprocessing Options
% 23.35/3.50  
% 23.35/3.50  --preprocessing_flag                    true
% 23.35/3.50  --time_out_prep_mult                    0.1
% 23.35/3.50  --splitting_mode                        input
% 23.35/3.50  --splitting_grd                         true
% 23.35/3.50  --splitting_cvd                         false
% 23.35/3.50  --splitting_cvd_svl                     false
% 23.35/3.50  --splitting_nvd                         32
% 23.35/3.50  --sub_typing                            true
% 23.35/3.50  --prep_gs_sim                           true
% 23.35/3.50  --prep_unflatten                        true
% 23.35/3.50  --prep_res_sim                          true
% 23.35/3.50  --prep_upred                            true
% 23.35/3.50  --prep_sem_filter                       exhaustive
% 23.35/3.50  --prep_sem_filter_out                   false
% 23.35/3.50  --pred_elim                             true
% 23.35/3.50  --res_sim_input                         true
% 23.35/3.50  --eq_ax_congr_red                       true
% 23.35/3.50  --pure_diseq_elim                       true
% 23.35/3.50  --brand_transform                       false
% 23.35/3.50  --non_eq_to_eq                          false
% 23.35/3.50  --prep_def_merge                        true
% 23.35/3.50  --prep_def_merge_prop_impl              false
% 23.35/3.50  --prep_def_merge_mbd                    true
% 23.35/3.50  --prep_def_merge_tr_red                 false
% 23.35/3.50  --prep_def_merge_tr_cl                  false
% 23.35/3.50  --smt_preprocessing                     true
% 23.35/3.50  --smt_ac_axioms                         fast
% 23.35/3.50  --preprocessed_out                      false
% 23.35/3.50  --preprocessed_stats                    false
% 23.35/3.50  
% 23.35/3.50  ------ Abstraction refinement Options
% 23.35/3.50  
% 23.35/3.50  --abstr_ref                             []
% 23.35/3.50  --abstr_ref_prep                        false
% 23.35/3.50  --abstr_ref_until_sat                   false
% 23.35/3.50  --abstr_ref_sig_restrict                funpre
% 23.35/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.35/3.50  --abstr_ref_under                       []
% 23.35/3.50  
% 23.35/3.50  ------ SAT Options
% 23.35/3.50  
% 23.35/3.50  --sat_mode                              false
% 23.35/3.50  --sat_fm_restart_options                ""
% 23.35/3.50  --sat_gr_def                            false
% 23.35/3.50  --sat_epr_types                         true
% 23.35/3.50  --sat_non_cyclic_types                  false
% 23.35/3.50  --sat_finite_models                     false
% 23.35/3.50  --sat_fm_lemmas                         false
% 23.35/3.50  --sat_fm_prep                           false
% 23.35/3.50  --sat_fm_uc_incr                        true
% 23.35/3.50  --sat_out_model                         small
% 23.35/3.50  --sat_out_clauses                       false
% 23.35/3.50  
% 23.35/3.50  ------ QBF Options
% 23.35/3.50  
% 23.35/3.50  --qbf_mode                              false
% 23.35/3.50  --qbf_elim_univ                         false
% 23.35/3.50  --qbf_dom_inst                          none
% 23.35/3.50  --qbf_dom_pre_inst                      false
% 23.35/3.50  --qbf_sk_in                             false
% 23.35/3.50  --qbf_pred_elim                         true
% 23.35/3.50  --qbf_split                             512
% 23.35/3.50  
% 23.35/3.50  ------ BMC1 Options
% 23.35/3.50  
% 23.35/3.50  --bmc1_incremental                      false
% 23.35/3.50  --bmc1_axioms                           reachable_all
% 23.35/3.50  --bmc1_min_bound                        0
% 23.35/3.50  --bmc1_max_bound                        -1
% 23.35/3.50  --bmc1_max_bound_default                -1
% 23.35/3.50  --bmc1_symbol_reachability              true
% 23.35/3.50  --bmc1_property_lemmas                  false
% 23.35/3.50  --bmc1_k_induction                      false
% 23.35/3.50  --bmc1_non_equiv_states                 false
% 23.35/3.50  --bmc1_deadlock                         false
% 23.35/3.50  --bmc1_ucm                              false
% 23.35/3.50  --bmc1_add_unsat_core                   none
% 23.35/3.50  --bmc1_unsat_core_children              false
% 23.35/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.35/3.50  --bmc1_out_stat                         full
% 23.35/3.50  --bmc1_ground_init                      false
% 23.35/3.50  --bmc1_pre_inst_next_state              false
% 23.35/3.50  --bmc1_pre_inst_state                   false
% 23.35/3.50  --bmc1_pre_inst_reach_state             false
% 23.35/3.50  --bmc1_out_unsat_core                   false
% 23.35/3.50  --bmc1_aig_witness_out                  false
% 23.35/3.50  --bmc1_verbose                          false
% 23.35/3.50  --bmc1_dump_clauses_tptp                false
% 23.35/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.35/3.50  --bmc1_dump_file                        -
% 23.35/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.35/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.35/3.50  --bmc1_ucm_extend_mode                  1
% 23.35/3.50  --bmc1_ucm_init_mode                    2
% 23.35/3.50  --bmc1_ucm_cone_mode                    none
% 23.35/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.35/3.50  --bmc1_ucm_relax_model                  4
% 23.35/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.35/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.35/3.50  --bmc1_ucm_layered_model                none
% 23.35/3.50  --bmc1_ucm_max_lemma_size               10
% 23.35/3.50  
% 23.35/3.50  ------ AIG Options
% 23.35/3.50  
% 23.35/3.50  --aig_mode                              false
% 23.35/3.50  
% 23.35/3.50  ------ Instantiation Options
% 23.35/3.50  
% 23.35/3.50  --instantiation_flag                    true
% 23.35/3.50  --inst_sos_flag                         false
% 23.35/3.50  --inst_sos_phase                        true
% 23.35/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.35/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.35/3.50  --inst_lit_sel_side                     none
% 23.35/3.50  --inst_solver_per_active                1400
% 23.35/3.50  --inst_solver_calls_frac                1.
% 23.35/3.50  --inst_passive_queue_type               priority_queues
% 23.35/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.35/3.50  --inst_passive_queues_freq              [25;2]
% 23.35/3.50  --inst_dismatching                      true
% 23.35/3.50  --inst_eager_unprocessed_to_passive     true
% 23.35/3.50  --inst_prop_sim_given                   true
% 23.35/3.50  --inst_prop_sim_new                     false
% 23.35/3.50  --inst_subs_new                         false
% 23.35/3.50  --inst_eq_res_simp                      false
% 23.35/3.50  --inst_subs_given                       false
% 23.35/3.50  --inst_orphan_elimination               true
% 23.35/3.50  --inst_learning_loop_flag               true
% 23.35/3.50  --inst_learning_start                   3000
% 23.35/3.50  --inst_learning_factor                  2
% 23.35/3.50  --inst_start_prop_sim_after_learn       3
% 23.35/3.50  --inst_sel_renew                        solver
% 23.35/3.50  --inst_lit_activity_flag                true
% 23.35/3.50  --inst_restr_to_given                   false
% 23.35/3.50  --inst_activity_threshold               500
% 23.35/3.50  --inst_out_proof                        true
% 23.35/3.50  
% 23.35/3.50  ------ Resolution Options
% 23.35/3.50  
% 23.35/3.50  --resolution_flag                       false
% 23.35/3.50  --res_lit_sel                           adaptive
% 23.35/3.50  --res_lit_sel_side                      none
% 23.35/3.50  --res_ordering                          kbo
% 23.35/3.50  --res_to_prop_solver                    active
% 23.35/3.50  --res_prop_simpl_new                    false
% 23.35/3.50  --res_prop_simpl_given                  true
% 23.35/3.50  --res_passive_queue_type                priority_queues
% 23.35/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.35/3.50  --res_passive_queues_freq               [15;5]
% 23.35/3.50  --res_forward_subs                      full
% 23.35/3.50  --res_backward_subs                     full
% 23.35/3.50  --res_forward_subs_resolution           true
% 23.35/3.50  --res_backward_subs_resolution          true
% 23.35/3.50  --res_orphan_elimination                true
% 23.35/3.50  --res_time_limit                        2.
% 23.35/3.50  --res_out_proof                         true
% 23.35/3.50  
% 23.35/3.50  ------ Superposition Options
% 23.35/3.50  
% 23.35/3.50  --superposition_flag                    true
% 23.35/3.50  --sup_passive_queue_type                priority_queues
% 23.35/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.35/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.35/3.50  --demod_completeness_check              fast
% 23.35/3.50  --demod_use_ground                      true
% 23.35/3.50  --sup_to_prop_solver                    passive
% 23.35/3.50  --sup_prop_simpl_new                    true
% 23.35/3.50  --sup_prop_simpl_given                  true
% 23.35/3.50  --sup_fun_splitting                     false
% 23.35/3.50  --sup_smt_interval                      50000
% 23.35/3.50  
% 23.35/3.50  ------ Superposition Simplification Setup
% 23.35/3.50  
% 23.35/3.50  --sup_indices_passive                   []
% 23.35/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.35/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.35/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.35/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.35/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.35/3.50  --sup_full_bw                           [BwDemod]
% 23.35/3.50  --sup_immed_triv                        [TrivRules]
% 23.35/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.35/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.35/3.50  --sup_immed_bw_main                     []
% 23.35/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.35/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.35/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.35/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.35/3.50  
% 23.35/3.50  ------ Combination Options
% 23.35/3.50  
% 23.35/3.50  --comb_res_mult                         3
% 23.35/3.50  --comb_sup_mult                         2
% 23.35/3.50  --comb_inst_mult                        10
% 23.35/3.50  
% 23.35/3.50  ------ Debug Options
% 23.35/3.50  
% 23.35/3.50  --dbg_backtrace                         false
% 23.35/3.50  --dbg_dump_prop_clauses                 false
% 23.35/3.50  --dbg_dump_prop_clauses_file            -
% 23.35/3.50  --dbg_out_stat                          false
% 23.35/3.50  
% 23.35/3.50  
% 23.35/3.50  
% 23.35/3.50  
% 23.35/3.50  ------ Proving...
% 23.35/3.50  
% 23.35/3.50  
% 23.35/3.50  % SZS status Theorem for theBenchmark.p
% 23.35/3.50  
% 23.35/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.35/3.50  
% 23.35/3.50  fof(f9,axiom,(
% 23.35/3.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,X1) <=> (! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 23.35/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.35/3.50  
% 23.35/3.50  fof(f24,plain,(
% 23.35/3.50    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.35/3.50    inference(ennf_transformation,[],[f9])).
% 23.35/3.50  
% 23.35/3.50  fof(f25,plain,(
% 23.35/3.50    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.35/3.50    inference(flattening,[],[f24])).
% 23.35/3.50  
% 23.35/3.50  fof(f40,plain,(
% 23.35/3.50    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) & ((! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.35/3.50    inference(nnf_transformation,[],[f25])).
% 23.35/3.50  
% 23.35/3.50  fof(f41,plain,(
% 23.35/3.50    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.35/3.50    inference(flattening,[],[f40])).
% 23.35/3.50  
% 23.35/3.50  fof(f42,plain,(
% 23.35/3.50    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.35/3.50    inference(rectify,[],[f41])).
% 23.35/3.50  
% 23.35/3.50  fof(f43,plain,(
% 23.35/3.50    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 23.35/3.50    introduced(choice_axiom,[])).
% 23.35/3.50  
% 23.35/3.50  fof(f44,plain,(
% 23.35/3.50    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.35/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).
% 23.35/3.50  
% 23.35/3.50  fof(f66,plain,(
% 23.35/3.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.35/3.50    inference(cnf_transformation,[],[f44])).
% 23.35/3.50  
% 23.35/3.50  fof(f13,conjecture,(
% 23.35/3.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 23.35/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.35/3.50  
% 23.35/3.50  fof(f14,negated_conjecture,(
% 23.35/3.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 23.35/3.50    inference(negated_conjecture,[],[f13])).
% 23.35/3.50  
% 23.35/3.50  fof(f31,plain,(
% 23.35/3.50    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 23.35/3.50    inference(ennf_transformation,[],[f14])).
% 23.35/3.50  
% 23.35/3.50  fof(f32,plain,(
% 23.35/3.50    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.35/3.50    inference(flattening,[],[f31])).
% 23.35/3.50  
% 23.35/3.50  fof(f47,plain,(
% 23.35/3.50    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK4) & ! [X3] : (k1_funct_1(sK4,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 23.35/3.50    introduced(choice_axiom,[])).
% 23.35/3.50  
% 23.35/3.50  fof(f46,plain,(
% 23.35/3.50    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k4_tmap_1(X0,sK3),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 23.35/3.50    introduced(choice_axiom,[])).
% 23.35/3.50  
% 23.35/3.50  fof(f45,plain,(
% 23.35/3.50    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK2),k4_tmap_1(sK2,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 23.35/3.50    introduced(choice_axiom,[])).
% 23.35/3.50  
% 23.35/3.50  fof(f48,plain,(
% 23.35/3.50    ((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) & ! [X3] : (k1_funct_1(sK4,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 23.35/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f47,f46,f45])).
% 23.35/3.50  
% 23.35/3.50  fof(f82,plain,(
% 23.35/3.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 23.35/3.50    inference(cnf_transformation,[],[f48])).
% 23.35/3.50  
% 23.35/3.50  fof(f7,axiom,(
% 23.35/3.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 23.35/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.35/3.50  
% 23.35/3.50  fof(f20,plain,(
% 23.35/3.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.35/3.50    inference(ennf_transformation,[],[f7])).
% 23.35/3.50  
% 23.35/3.50  fof(f21,plain,(
% 23.35/3.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.35/3.50    inference(flattening,[],[f20])).
% 23.35/3.50  
% 23.35/3.50  fof(f35,plain,(
% 23.35/3.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.35/3.50    inference(nnf_transformation,[],[f21])).
% 23.35/3.50  
% 23.35/3.50  fof(f57,plain,(
% 23.35/3.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.35/3.50    inference(cnf_transformation,[],[f35])).
% 23.35/3.50  
% 23.35/3.50  fof(f6,axiom,(
% 23.35/3.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 23.35/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.35/3.50  
% 23.35/3.50  fof(f19,plain,(
% 23.35/3.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.35/3.50    inference(ennf_transformation,[],[f6])).
% 23.35/3.50  
% 23.35/3.50  fof(f56,plain,(
% 23.35/3.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.35/3.50    inference(cnf_transformation,[],[f19])).
% 23.35/3.50  
% 23.35/3.50  fof(f81,plain,(
% 23.35/3.50    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 23.35/3.50    inference(cnf_transformation,[],[f48])).
% 23.35/3.50  
% 23.35/3.50  fof(f79,plain,(
% 23.35/3.50    m1_pre_topc(sK3,sK2)),
% 23.35/3.50    inference(cnf_transformation,[],[f48])).
% 23.35/3.50  
% 23.35/3.50  fof(f10,axiom,(
% 23.35/3.50    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 23.35/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.35/3.50  
% 23.35/3.50  fof(f26,plain,(
% 23.35/3.50    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.35/3.50    inference(ennf_transformation,[],[f10])).
% 23.35/3.50  
% 23.35/3.50  fof(f27,plain,(
% 23.35/3.50    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.35/3.50    inference(flattening,[],[f26])).
% 23.35/3.50  
% 23.35/3.50  fof(f72,plain,(
% 23.35/3.50    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.35/3.50    inference(cnf_transformation,[],[f27])).
% 23.35/3.50  
% 23.35/3.50  fof(f76,plain,(
% 23.35/3.50    v2_pre_topc(sK2)),
% 23.35/3.50    inference(cnf_transformation,[],[f48])).
% 23.35/3.50  
% 23.35/3.50  fof(f75,plain,(
% 23.35/3.50    ~v2_struct_0(sK2)),
% 23.35/3.50    inference(cnf_transformation,[],[f48])).
% 23.35/3.50  
% 23.35/3.50  fof(f77,plain,(
% 23.35/3.50    l1_pre_topc(sK2)),
% 23.35/3.50    inference(cnf_transformation,[],[f48])).
% 23.35/3.50  
% 23.35/3.50  fof(f61,plain,(
% 23.35/3.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.35/3.50    inference(cnf_transformation,[],[f35])).
% 23.35/3.50  
% 23.35/3.50  fof(f89,plain,(
% 23.35/3.50    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 23.35/3.50    inference(equality_resolution,[],[f61])).
% 23.35/3.50  
% 23.35/3.50  fof(f80,plain,(
% 23.35/3.50    v1_funct_1(sK4)),
% 23.35/3.50    inference(cnf_transformation,[],[f48])).
% 23.35/3.50  
% 23.35/3.50  fof(f70,plain,(
% 23.35/3.50    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.35/3.50    inference(cnf_transformation,[],[f27])).
% 23.35/3.50  
% 23.35/3.50  fof(f71,plain,(
% 23.35/3.50    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.35/3.50    inference(cnf_transformation,[],[f27])).
% 23.35/3.50  
% 23.35/3.50  fof(f8,axiom,(
% 23.35/3.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 23.35/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.35/3.50  
% 23.35/3.50  fof(f22,plain,(
% 23.35/3.50    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 23.35/3.50    inference(ennf_transformation,[],[f8])).
% 23.35/3.50  
% 23.35/3.50  fof(f23,plain,(
% 23.35/3.50    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 23.35/3.50    inference(flattening,[],[f22])).
% 23.35/3.50  
% 23.35/3.50  fof(f36,plain,(
% 23.35/3.50    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 23.35/3.50    inference(nnf_transformation,[],[f23])).
% 23.35/3.50  
% 23.35/3.50  fof(f37,plain,(
% 23.35/3.50    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 23.35/3.50    inference(rectify,[],[f36])).
% 23.35/3.50  
% 23.35/3.50  fof(f38,plain,(
% 23.35/3.50    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0)))),
% 23.35/3.50    introduced(choice_axiom,[])).
% 23.35/3.50  
% 23.35/3.50  fof(f39,plain,(
% 23.35/3.50    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 23.35/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 23.35/3.50  
% 23.35/3.50  fof(f65,plain,(
% 23.35/3.50    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 23.35/3.50    inference(cnf_transformation,[],[f39])).
% 23.35/3.50  
% 23.35/3.50  fof(f84,plain,(
% 23.35/3.50    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4)),
% 23.35/3.50    inference(cnf_transformation,[],[f48])).
% 23.35/3.50  
% 23.35/3.50  fof(f68,plain,(
% 23.35/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.35/3.50    inference(cnf_transformation,[],[f44])).
% 23.35/3.50  
% 23.35/3.50  fof(f4,axiom,(
% 23.35/3.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 23.35/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.35/3.50  
% 23.35/3.50  fof(f18,plain,(
% 23.35/3.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 23.35/3.50    inference(ennf_transformation,[],[f4])).
% 23.35/3.50  
% 23.35/3.50  fof(f54,plain,(
% 23.35/3.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 23.35/3.50    inference(cnf_transformation,[],[f18])).
% 23.35/3.50  
% 23.35/3.50  fof(f5,axiom,(
% 23.35/3.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 23.35/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.35/3.50  
% 23.35/3.50  fof(f55,plain,(
% 23.35/3.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 23.35/3.50    inference(cnf_transformation,[],[f5])).
% 23.35/3.50  
% 23.35/3.50  fof(f11,axiom,(
% 23.35/3.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.35/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.35/3.50  
% 23.35/3.50  fof(f28,plain,(
% 23.35/3.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.35/3.50    inference(ennf_transformation,[],[f11])).
% 23.35/3.50  
% 23.35/3.50  fof(f73,plain,(
% 23.35/3.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.35/3.50    inference(cnf_transformation,[],[f28])).
% 23.35/3.50  
% 23.35/3.50  fof(f3,axiom,(
% 23.35/3.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 23.35/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.35/3.50  
% 23.35/3.50  fof(f16,plain,(
% 23.35/3.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 23.35/3.50    inference(ennf_transformation,[],[f3])).
% 23.35/3.50  
% 23.35/3.50  fof(f17,plain,(
% 23.35/3.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 23.35/3.50    inference(flattening,[],[f16])).
% 23.35/3.50  
% 23.35/3.50  fof(f53,plain,(
% 23.35/3.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 23.35/3.50    inference(cnf_transformation,[],[f17])).
% 23.35/3.50  
% 23.35/3.50  fof(f83,plain,(
% 23.35/3.50    ( ! [X3] : (k1_funct_1(sK4,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK2))) )),
% 23.35/3.50    inference(cnf_transformation,[],[f48])).
% 23.35/3.50  
% 23.35/3.50  fof(f1,axiom,(
% 23.35/3.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.35/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.35/3.50  
% 23.35/3.50  fof(f33,plain,(
% 23.35/3.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.35/3.50    inference(nnf_transformation,[],[f1])).
% 23.35/3.50  
% 23.35/3.50  fof(f34,plain,(
% 23.35/3.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.35/3.50    inference(flattening,[],[f33])).
% 23.35/3.50  
% 23.35/3.50  fof(f49,plain,(
% 23.35/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.35/3.50    inference(cnf_transformation,[],[f34])).
% 23.35/3.50  
% 23.35/3.50  fof(f86,plain,(
% 23.35/3.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.35/3.50    inference(equality_resolution,[],[f49])).
% 23.35/3.50  
% 23.35/3.50  fof(f51,plain,(
% 23.35/3.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.35/3.50    inference(cnf_transformation,[],[f34])).
% 23.35/3.50  
% 23.35/3.50  fof(f50,plain,(
% 23.35/3.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 23.35/3.50    inference(cnf_transformation,[],[f34])).
% 23.35/3.50  
% 23.35/3.50  fof(f85,plain,(
% 23.35/3.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.35/3.50    inference(equality_resolution,[],[f50])).
% 23.35/3.50  
% 23.35/3.50  fof(f67,plain,(
% 23.35/3.50    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_tarski(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.35/3.50    inference(cnf_transformation,[],[f44])).
% 23.35/3.50  
% 23.35/3.50  fof(f69,plain,(
% 23.35/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.35/3.50    inference(cnf_transformation,[],[f44])).
% 23.35/3.50  
% 23.35/3.50  fof(f12,axiom,(
% 23.35/3.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 23.35/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.35/3.50  
% 23.35/3.50  fof(f29,plain,(
% 23.35/3.50    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.35/3.50    inference(ennf_transformation,[],[f12])).
% 23.35/3.50  
% 23.35/3.50  fof(f30,plain,(
% 23.35/3.50    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.35/3.50    inference(flattening,[],[f29])).
% 23.35/3.50  
% 23.35/3.50  fof(f74,plain,(
% 23.35/3.50    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.35/3.50    inference(cnf_transformation,[],[f30])).
% 23.35/3.50  
% 23.35/3.50  fof(f78,plain,(
% 23.35/3.50    ~v2_struct_0(sK3)),
% 23.35/3.50    inference(cnf_transformation,[],[f48])).
% 23.35/3.50  
% 23.35/3.50  fof(f58,plain,(
% 23.35/3.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.35/3.50    inference(cnf_transformation,[],[f35])).
% 23.35/3.50  
% 23.35/3.50  fof(f91,plain,(
% 23.35/3.50    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 23.35/3.50    inference(equality_resolution,[],[f58])).
% 23.35/3.50  
% 23.35/3.50  cnf(c_20,plain,
% 23.35/3.50      ( ~ r1_tarski(X0,X1)
% 23.35/3.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 23.35/3.50      | ~ v1_funct_1(X1)
% 23.35/3.50      | ~ v1_funct_1(X0)
% 23.35/3.50      | ~ v1_relat_1(X0)
% 23.35/3.50      | ~ v1_relat_1(X1) ),
% 23.35/3.50      inference(cnf_transformation,[],[f66]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1775,plain,
% 23.35/3.50      ( r1_tarski(X0,X1) != iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 23.35/3.50      | v1_funct_1(X1) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_28,negated_conjecture,
% 23.35/3.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 23.35/3.50      inference(cnf_transformation,[],[f82]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1773,plain,
% 23.35/3.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_13,plain,
% 23.35/3.50      ( ~ v1_funct_2(X0,X1,X2)
% 23.35/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.35/3.50      | k1_relset_1(X1,X2,X0) = X1
% 23.35/3.50      | k1_xboole_0 = X2 ),
% 23.35/3.50      inference(cnf_transformation,[],[f57]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1779,plain,
% 23.35/3.50      ( k1_relset_1(X0,X1,X2) = X0
% 23.35/3.50      | k1_xboole_0 = X1
% 23.35/3.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 23.35/3.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3609,plain,
% 23.35/3.50      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),sK4) = u1_struct_0(sK3)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_1773,c_1779]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_7,plain,
% 23.35/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.35/3.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 23.35/3.50      inference(cnf_transformation,[],[f56]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1785,plain,
% 23.35/3.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 23.35/3.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2431,plain,
% 23.35/3.50      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),sK4) = k1_relat_1(sK4) ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_1773,c_1785]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3621,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_relat_1(sK4)
% 23.35/3.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(light_normalisation,[status(thm)],[c_3609,c_2431]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_29,negated_conjecture,
% 23.35/3.50      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 23.35/3.50      inference(cnf_transformation,[],[f81]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3626,plain,
% 23.35/3.50      ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_relat_1(sK4) ),
% 23.35/3.50      inference(predicate_to_equality_rev,[status(thm)],[c_3621]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3856,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_relat_1(sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0 ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_3621,c_29,c_3626]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3857,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_relat_1(sK4) ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_3856]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_31,negated_conjecture,
% 23.35/3.50      ( m1_pre_topc(sK3,sK2) ),
% 23.35/3.50      inference(cnf_transformation,[],[f79]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_21,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.35/3.50      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 23.35/3.50      | v2_struct_0(X1)
% 23.35/3.50      | ~ v2_pre_topc(X1)
% 23.35/3.50      | ~ l1_pre_topc(X1) ),
% 23.35/3.50      inference(cnf_transformation,[],[f72]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_34,negated_conjecture,
% 23.35/3.50      ( v2_pre_topc(sK2) ),
% 23.35/3.50      inference(cnf_transformation,[],[f76]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_455,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.35/3.50      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 23.35/3.50      | v2_struct_0(X1)
% 23.35/3.50      | ~ l1_pre_topc(X1)
% 23.35/3.50      | sK2 != X1 ),
% 23.35/3.50      inference(resolution_lifted,[status(thm)],[c_21,c_34]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_456,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,sK2)
% 23.35/3.50      | m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
% 23.35/3.50      | v2_struct_0(sK2)
% 23.35/3.50      | ~ l1_pre_topc(sK2) ),
% 23.35/3.50      inference(unflattening,[status(thm)],[c_455]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_35,negated_conjecture,
% 23.35/3.50      ( ~ v2_struct_0(sK2) ),
% 23.35/3.50      inference(cnf_transformation,[],[f75]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_33,negated_conjecture,
% 23.35/3.50      ( l1_pre_topc(sK2) ),
% 23.35/3.50      inference(cnf_transformation,[],[f77]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_460,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,sK2)
% 23.35/3.50      | m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_456,c_35,c_33]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_510,plain,
% 23.35/3.50      ( m1_subset_1(k4_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
% 23.35/3.50      | sK2 != sK2
% 23.35/3.50      | sK3 != X0 ),
% 23.35/3.50      inference(resolution_lifted,[status(thm)],[c_31,c_460]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_511,plain,
% 23.35/3.50      ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 23.35/3.50      inference(unflattening,[status(thm)],[c_510]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1769,plain,
% 23.35/3.50      ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3865,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_relat_1(sK4)
% 23.35/3.50      | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0))) = iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_3857,c_1769]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_9,plain,
% 23.35/3.50      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 23.35/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 23.35/3.50      | k1_xboole_0 = X1
% 23.35/3.50      | k1_xboole_0 = X0 ),
% 23.35/3.50      inference(cnf_transformation,[],[f89]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1783,plain,
% 23.35/3.50      ( k1_xboole_0 = X0
% 23.35/3.50      | k1_xboole_0 = X1
% 23.35/3.50      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 23.35/3.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_4217,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_relat_1(sK4)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),k1_xboole_0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_3865,c_1783]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_30,negated_conjecture,
% 23.35/3.50      ( v1_funct_1(sK4) ),
% 23.35/3.50      inference(cnf_transformation,[],[f80]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_23,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.35/3.50      | v2_struct_0(X1)
% 23.35/3.50      | ~ v2_pre_topc(X1)
% 23.35/3.50      | ~ l1_pre_topc(X1)
% 23.35/3.50      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 23.35/3.50      inference(cnf_transformation,[],[f70]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_437,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.35/3.50      | v2_struct_0(X1)
% 23.35/3.50      | ~ l1_pre_topc(X1)
% 23.35/3.50      | v1_funct_1(k4_tmap_1(X1,X0))
% 23.35/3.50      | sK2 != X1 ),
% 23.35/3.50      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_438,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,sK2)
% 23.35/3.50      | v2_struct_0(sK2)
% 23.35/3.50      | ~ l1_pre_topc(sK2)
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,X0)) ),
% 23.35/3.50      inference(unflattening,[status(thm)],[c_437]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_442,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,sK2) | v1_funct_1(k4_tmap_1(sK2,X0)) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_438,c_35,c_33]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_517,plain,
% 23.35/3.50      ( v1_funct_1(k4_tmap_1(sK2,X0)) | sK2 != sK2 | sK3 != X0 ),
% 23.35/3.50      inference(resolution_lifted,[status(thm)],[c_31,c_442]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_518,plain,
% 23.35/3.50      ( v1_funct_1(k4_tmap_1(sK2,sK3)) ),
% 23.35/3.50      inference(unflattening,[status(thm)],[c_517]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_22,plain,
% 23.35/3.50      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 23.35/3.50      | ~ m1_pre_topc(X1,X0)
% 23.35/3.50      | v2_struct_0(X0)
% 23.35/3.50      | ~ v2_pre_topc(X0)
% 23.35/3.50      | ~ l1_pre_topc(X0) ),
% 23.35/3.50      inference(cnf_transformation,[],[f71]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_392,plain,
% 23.35/3.50      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 23.35/3.50      | ~ m1_pre_topc(X1,X0)
% 23.35/3.50      | v2_struct_0(X0)
% 23.35/3.50      | ~ l1_pre_topc(X0)
% 23.35/3.50      | sK2 != X0 ),
% 23.35/3.50      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_393,plain,
% 23.35/3.50      ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
% 23.35/3.50      | ~ m1_pre_topc(X0,sK2)
% 23.35/3.50      | v2_struct_0(sK2)
% 23.35/3.50      | ~ l1_pre_topc(sK2) ),
% 23.35/3.50      inference(unflattening,[status(thm)],[c_392]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_397,plain,
% 23.35/3.50      ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
% 23.35/3.50      | ~ m1_pre_topc(X0,sK2) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_393,c_35,c_33]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_545,plain,
% 23.35/3.50      ( v1_funct_2(k4_tmap_1(sK2,X0),u1_struct_0(X0),u1_struct_0(sK2))
% 23.35/3.50      | sK2 != sK2
% 23.35/3.50      | sK3 != X0 ),
% 23.35/3.50      inference(resolution_lifted,[status(thm)],[c_31,c_397]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_546,plain,
% 23.35/3.50      ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 23.35/3.50      inference(unflattening,[status(thm)],[c_545]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_14,plain,
% 23.35/3.50      ( r2_funct_2(X0,X1,X2,X3)
% 23.35/3.50      | ~ v1_funct_2(X2,X0,X1)
% 23.35/3.50      | ~ v1_funct_2(X3,X0,X1)
% 23.35/3.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.35/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.35/3.50      | ~ v1_funct_1(X3)
% 23.35/3.50      | ~ v1_funct_1(X2)
% 23.35/3.50      | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
% 23.35/3.50      inference(cnf_transformation,[],[f65]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_26,negated_conjecture,
% 23.35/3.50      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) ),
% 23.35/3.50      inference(cnf_transformation,[],[f84]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_830,plain,
% 23.35/3.50      ( ~ v1_funct_2(X0,X1,X2)
% 23.35/3.50      | ~ v1_funct_2(X3,X1,X2)
% 23.35/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.35/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.35/3.50      | ~ v1_funct_1(X3)
% 23.35/3.50      | ~ v1_funct_1(X0)
% 23.35/3.50      | k4_tmap_1(sK2,sK3) != X0
% 23.35/3.50      | k1_funct_1(X3,sK0(X1,X0,X3)) != k1_funct_1(X0,sK0(X1,X0,X3))
% 23.35/3.50      | u1_struct_0(sK2) != X2
% 23.35/3.50      | u1_struct_0(sK3) != X1
% 23.35/3.50      | sK4 != X3 ),
% 23.35/3.50      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_831,plain,
% 23.35/3.50      ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 23.35/3.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 23.35/3.50      | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
% 23.35/3.50      | ~ v1_funct_1(sK4)
% 23.35/3.50      | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) != k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) ),
% 23.35/3.50      inference(unflattening,[status(thm)],[c_830]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1256,plain,
% 23.35/3.50      ( X0 != X1 | X2 != X3 | k1_funct_1(X0,X2) = k1_funct_1(X1,X3) ),
% 23.35/3.50      theory(equality) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2122,plain,
% 23.35/3.50      ( sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) != sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(sK4,sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4)) = k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4))
% 23.35/3.50      | sK4 != k4_tmap_1(sK2,sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1256]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1246,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2250,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) != X0 | sK4 != X0 | sK4 = k4_tmap_1(sK2,sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1246]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2251,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) != k1_xboole_0
% 23.35/3.50      | sK4 = k4_tmap_1(sK2,sK3)
% 23.35/3.50      | sK4 != k1_xboole_0 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2250]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1766,plain,
% 23.35/3.50      ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3867,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_relat_1(sK4)
% 23.35/3.50      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),k1_xboole_0) = iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_3857,c_1766]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3942,plain,
% 23.35/3.50      ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),k1_xboole_0)
% 23.35/3.50      | u1_struct_0(sK3) = k1_relat_1(sK4) ),
% 23.35/3.50      inference(predicate_to_equality_rev,[status(thm)],[c_3867]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_4245,plain,
% 23.35/3.50      ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),k1_xboole_0)
% 23.35/3.50      | k4_tmap_1(sK2,sK3) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_relat_1(sK4)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(predicate_to_equality_rev,[status(thm)],[c_4217]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3869,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_relat_1(sK4)
% 23.35/3.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0))) = iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_3857,c_1773]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_4035,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_relat_1(sK4)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | sK4 = k1_xboole_0
% 23.35/3.50      | v1_funct_2(sK4,u1_struct_0(sK3),k1_xboole_0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_3869,c_1783]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1772,plain,
% 23.35/3.50      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3870,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_relat_1(sK4)
% 23.35/3.50      | v1_funct_2(sK4,u1_struct_0(sK3),k1_xboole_0) = iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_3857,c_1772]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_4475,plain,
% 23.35/3.50      ( sK4 = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_relat_1(sK4) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_4035,c_3870]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_4476,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_relat_1(sK4)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | sK4 = k1_xboole_0 ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_4475]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1245,plain,( X0 = X0 ),theory(equality) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5589,plain,
% 23.35/3.50      ( sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) = sK0(u1_struct_0(sK3),k4_tmap_1(sK2,sK3),sK4) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1245]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5647,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_relat_1(sK4) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_4217,c_30,c_29,c_28,c_511,c_518,c_546,c_831,c_2122,
% 23.35/3.50                 c_2251,c_3942,c_4245,c_4476,c_5589]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5648,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_relat_1(sK4)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_5647]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3610,plain,
% 23.35/3.50      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_1769,c_1779]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2533,plain,
% 23.35/3.50      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(k4_tmap_1(sK2,sK3)) ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_1769,c_1785]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3614,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
% 23.35/3.50      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(demodulation,[status(thm)],[c_3610,c_2533]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3625,plain,
% 23.35/3.50      ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3) ),
% 23.35/3.50      inference(predicate_to_equality_rev,[status(thm)],[c_3614]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_7698,plain,
% 23.35/3.50      ( k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0 ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_3614,c_546,c_3625]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_7699,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | k1_relat_1(k4_tmap_1(sK2,sK3)) = u1_struct_0(sK3) ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_7698]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_18,plain,
% 23.35/3.50      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 23.35/3.50      | r1_tarski(X0,X1)
% 23.35/3.50      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 23.35/3.50      | ~ v1_funct_1(X1)
% 23.35/3.50      | ~ v1_funct_1(X0)
% 23.35/3.50      | ~ v1_relat_1(X0)
% 23.35/3.50      | ~ v1_relat_1(X1) ),
% 23.35/3.50      inference(cnf_transformation,[],[f68]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1777,plain,
% 23.35/3.50      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 23.35/3.50      | r1_tarski(X0,X1) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 23.35/3.50      | v1_funct_1(X1) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_7703,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK3)) = iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_7699,c_1777]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_512,plain,
% 23.35/3.50      ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_519,plain,
% 23.35/3.50      ( v1_funct_1(k4_tmap_1(sK2,sK3)) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_518]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5,plain,
% 23.35/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.35/3.50      | ~ v1_relat_1(X1)
% 23.35/3.50      | v1_relat_1(X0) ),
% 23.35/3.50      inference(cnf_transformation,[],[f54]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2052,plain,
% 23.35/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.35/3.50      | v1_relat_1(X0)
% 23.35/3.50      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_5]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2223,plain,
% 23.35/3.50      ( ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3))
% 23.35/3.50      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2052]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2224,plain,
% 23.35/3.50      ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_2223]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_6,plain,
% 23.35/3.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 23.35/3.50      inference(cnf_transformation,[],[f55]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2298,plain,
% 23.35/3.50      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_6]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2299,plain,
% 23.35/3.50      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_2298]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_10451,plain,
% 23.35/3.50      ( v1_relat_1(X0) != iProver_top
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK3)) = iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_7703,c_512,c_519,c_2224,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_10452,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK3)) = iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_10451]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_24,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.35/3.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.35/3.50      | ~ l1_pre_topc(X1) ),
% 23.35/3.50      inference(cnf_transformation,[],[f73]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_488,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.35/3.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.35/3.50      | sK2 != X1 ),
% 23.35/3.50      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_489,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,sK2)
% 23.35/3.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 23.35/3.50      inference(unflattening,[status(thm)],[c_488]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_503,plain,
% 23.35/3.50      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 23.35/3.50      | sK2 != sK2
% 23.35/3.50      | sK3 != X0 ),
% 23.35/3.50      inference(resolution_lifted,[status(thm)],[c_31,c_489]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_504,plain,
% 23.35/3.50      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 23.35/3.50      inference(unflattening,[status(thm)],[c_503]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1770,plain,
% 23.35/3.50      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_4,plain,
% 23.35/3.50      ( ~ r2_hidden(X0,X1)
% 23.35/3.50      | m1_subset_1(X0,X2)
% 23.35/3.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 23.35/3.50      inference(cnf_transformation,[],[f53]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1788,plain,
% 23.35/3.50      ( r2_hidden(X0,X1) != iProver_top
% 23.35/3.50      | m1_subset_1(X0,X2) = iProver_top
% 23.35/3.50      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2914,plain,
% 23.35/3.50      ( r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
% 23.35/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_1770,c_1788]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_10466,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) = iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_10452,c_2914]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_27,negated_conjecture,
% 23.35/3.50      ( ~ r2_hidden(X0,u1_struct_0(sK3))
% 23.35/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 23.35/3.50      | k1_funct_1(sK4,X0) = X0 ),
% 23.35/3.50      inference(cnf_transformation,[],[f83]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1774,plain,
% 23.35/3.50      ( k1_funct_1(sK4,X0) = X0
% 23.35/3.50      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
% 23.35/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_10468,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_10452,c_1774]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_10505,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(backward_subsumption_resolution,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_10466,c_10468]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_10786,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_7699,c_10505]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_10858,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_5648,c_10786]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_19807,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_1775,c_10858]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_41,plain,
% 23.35/3.50      ( v1_funct_1(sK4) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_43,plain,
% 23.35/3.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2220,plain,
% 23.35/3.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 23.35/3.50      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
% 23.35/3.50      | v1_relat_1(sK4) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2052]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2221,plain,
% 23.35/3.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 23.35/3.50      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_2220]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_19948,plain,
% 23.35/3.50      ( v1_relat_1(X0) != iProver_top
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_19807,c_41,c_43,c_2221,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_19949,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_19948]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_7705,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) != iProver_top
% 23.35/3.50      | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_7699,c_1775]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_7907,plain,
% 23.35/3.50      ( v1_relat_1(X0) != iProver_top
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) != iProver_top
% 23.35/3.50      | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_7705,c_512,c_519,c_2224,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_7908,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) != iProver_top
% 23.35/3.50      | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_7907]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_19976,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) = iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_19949,c_7908]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2,plain,
% 23.35/3.50      ( r1_tarski(X0,X0) ),
% 23.35/3.50      inference(cnf_transformation,[],[f86]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_116,plain,
% 23.35/3.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_0,plain,
% 23.35/3.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.35/3.50      inference(cnf_transformation,[],[f51]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_120,plain,
% 23.35/3.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 23.35/3.50      | k1_xboole_0 = k1_xboole_0 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_0]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2184,plain,
% 23.35/3.50      ( sK4 = sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1245]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2414,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1245]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2444,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = k4_tmap_1(sK2,sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1245]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2512,plain,
% 23.35/3.50      ( X0 != X1 | X0 = u1_struct_0(sK2) | u1_struct_0(sK2) != X1 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1246]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2513,plain,
% 23.35/3.50      ( u1_struct_0(sK2) != k1_xboole_0
% 23.35/3.50      | k1_xboole_0 = u1_struct_0(sK2)
% 23.35/3.50      | k1_xboole_0 != k1_xboole_0 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2512]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2481,plain,
% 23.35/3.50      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1246]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3064,plain,
% 23.35/3.50      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2481]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3065,plain,
% 23.35/3.50      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_3064]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2658,plain,
% 23.35/3.50      ( X0 != X1 | k4_tmap_1(sK2,sK3) != X1 | k4_tmap_1(sK2,sK3) = X0 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1246]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3681,plain,
% 23.35/3.50      ( X0 != k4_tmap_1(sK2,sK3)
% 23.35/3.50      | k4_tmap_1(sK2,sK3) = X0
% 23.35/3.50      | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2658]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3682,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
% 23.35/3.50      | k4_tmap_1(sK2,sK3) = k1_xboole_0
% 23.35/3.50      | k1_xboole_0 != k4_tmap_1(sK2,sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_3681]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1254,plain,
% 23.35/3.50      ( ~ v1_funct_2(X0,X1,X2)
% 23.35/3.50      | v1_funct_2(X3,X4,X5)
% 23.35/3.50      | X3 != X0
% 23.35/3.50      | X4 != X1
% 23.35/3.50      | X5 != X2 ),
% 23.35/3.50      theory(equality) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2130,plain,
% 23.35/3.50      ( v1_funct_2(X0,X1,X2)
% 23.35/3.50      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | X2 != u1_struct_0(sK2)
% 23.35/3.50      | X1 != u1_struct_0(sK3)
% 23.35/3.50      | X0 != sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1254]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2312,plain,
% 23.35/3.50      ( v1_funct_2(sK4,X0,X1)
% 23.35/3.50      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | X1 != u1_struct_0(sK2)
% 23.35/3.50      | X0 != u1_struct_0(sK3)
% 23.35/3.50      | sK4 != sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2130]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_4100,plain,
% 23.35/3.50      ( v1_funct_2(sK4,u1_struct_0(sK3),X0)
% 23.35/3.50      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | X0 != u1_struct_0(sK2)
% 23.35/3.50      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 23.35/3.50      | sK4 != sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2312]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_4102,plain,
% 23.35/3.50      ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | v1_funct_2(sK4,u1_struct_0(sK3),k1_xboole_0)
% 23.35/3.50      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 23.35/3.50      | sK4 != sK4
% 23.35/3.50      | k1_xboole_0 != u1_struct_0(sK2) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_4100]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1252,plain,
% 23.35/3.50      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 23.35/3.50      theory(equality) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3001,plain,
% 23.35/3.50      ( X0 != u1_struct_0(sK2)
% 23.35/3.50      | X1 != u1_struct_0(sK3)
% 23.35/3.50      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1252]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_4971,plain,
% 23.35/3.50      ( X0 != u1_struct_0(sK2)
% 23.35/3.50      | k2_zfmisc_1(u1_struct_0(sK3),X0) = k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_3001]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_4972,plain,
% 23.35/3.50      ( k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0) = k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 23.35/3.50      | k1_xboole_0 != u1_struct_0(sK2) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_4971]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2135,plain,
% 23.35/3.50      ( v1_funct_2(X0,X1,X2)
% 23.35/3.50      | ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | X0 != k4_tmap_1(sK2,sK3)
% 23.35/3.50      | X2 != u1_struct_0(sK2)
% 23.35/3.50      | X1 != u1_struct_0(sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1254]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_4142,plain,
% 23.35/3.50      ( v1_funct_2(X0,u1_struct_0(sK3),X1)
% 23.35/3.50      | ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | X0 != k4_tmap_1(sK2,sK3)
% 23.35/3.50      | X1 != u1_struct_0(sK2)
% 23.35/3.50      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2135]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5899,plain,
% 23.35/3.50      ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),X0)
% 23.35/3.50      | ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | X0 != u1_struct_0(sK2)
% 23.35/3.50      | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
% 23.35/3.50      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_4142]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5901,plain,
% 23.35/3.50      ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),k1_xboole_0)
% 23.35/3.50      | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
% 23.35/3.50      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 23.35/3.50      | k1_xboole_0 != u1_struct_0(sK2) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_5899]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3009,plain,
% 23.35/3.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),k1_xboole_0)
% 23.35/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)))
% 23.35/3.50      | k1_xboole_0 = X0
% 23.35/3.50      | k1_xboole_0 = u1_struct_0(sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_9]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_6153,plain,
% 23.35/3.50      ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),k1_xboole_0)
% 23.35/3.50      | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)))
% 23.35/3.50      | k1_xboole_0 = k4_tmap_1(sK2,sK3)
% 23.35/3.50      | k1_xboole_0 = u1_struct_0(sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_3009]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3286,plain,
% 23.35/3.50      ( X0 != X1 | u1_struct_0(sK3) != X1 | u1_struct_0(sK3) = X0 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1246]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_6808,plain,
% 23.35/3.50      ( X0 != u1_struct_0(sK3)
% 23.35/3.50      | u1_struct_0(sK3) = X0
% 23.35/3.50      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_3286]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_6809,plain,
% 23.35/3.50      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | k1_xboole_0 != u1_struct_0(sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_6808]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_8566,plain,
% 23.35/3.50      ( ~ v1_funct_2(sK4,u1_struct_0(sK3),k1_xboole_0)
% 23.35/3.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)))
% 23.35/3.50      | k1_xboole_0 = u1_struct_0(sK3)
% 23.35/3.50      | k1_xboole_0 = sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_3009]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1250,plain,
% 23.35/3.50      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 23.35/3.50      theory(equality) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2362,plain,
% 23.35/3.50      ( X0 != k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1250]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3000,plain,
% 23.35/3.50      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2362]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_11493,plain,
% 23.35/3.50      ( k2_zfmisc_1(u1_struct_0(sK3),X0) != k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_3000]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_11494,plain,
% 23.35/3.50      ( k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0) != k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_11493]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1248,plain,
% 23.35/3.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.35/3.50      theory(equality) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2112,plain,
% 23.35/3.50      ( m1_subset_1(X0,X1)
% 23.35/3.50      | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 23.35/3.50      | X0 != k4_tmap_1(sK2,sK3)
% 23.35/3.50      | X1 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1248]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2443,plain,
% 23.35/3.50      ( m1_subset_1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 23.35/3.50      | X0 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
% 23.35/3.50      | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2112]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_43162,plain,
% 23.35/3.50      ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0)))
% 23.35/3.50      | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 23.35/3.50      | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
% 23.35/3.50      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2443]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_43165,plain,
% 23.35/3.50      ( ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 23.35/3.50      | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)))
% 23.35/3.50      | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
% 23.35/3.50      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_43162]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2102,plain,
% 23.35/3.50      ( m1_subset_1(X0,X1)
% 23.35/3.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 23.35/3.50      | X1 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
% 23.35/3.50      | X0 != sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1248]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2183,plain,
% 23.35/3.50      ( m1_subset_1(sK4,X0)
% 23.35/3.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 23.35/3.50      | X0 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
% 23.35/3.50      | sK4 != sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2102]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2361,plain,
% 23.35/3.50      ( m1_subset_1(sK4,k1_zfmisc_1(X0))
% 23.35/3.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 23.35/3.50      | k1_zfmisc_1(X0) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
% 23.35/3.50      | sK4 != sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2183]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_43177,plain,
% 23.35/3.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0)))
% 23.35/3.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 23.35/3.50      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
% 23.35/3.50      | sK4 != sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2361]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_43179,plain,
% 23.35/3.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 23.35/3.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)))
% 23.35/3.50      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
% 23.35/3.50      | sK4 != sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_43177]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54629,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) = iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_19976,c_30,c_29,c_28,c_116,c_120,c_511,c_518,c_546,
% 23.35/3.50                 c_831,c_2122,c_2184,c_2251,c_2414,c_2444,c_2513,c_3065,
% 23.35/3.50                 c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,
% 23.35/3.50                 c_11494,c_43165,c_43179]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1791,plain,
% 23.35/3.50      ( X0 = X1
% 23.35/3.50      | r1_tarski(X0,X1) != iProver_top
% 23.35/3.50      | r1_tarski(X1,X0) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54648,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | k1_relat_1(X0) = u1_struct_0(sK3)
% 23.35/3.50      | r1_tarski(k1_relat_1(X0),u1_struct_0(sK3)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_54629,c_1791]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2608,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) != sK4
% 23.35/3.50      | sK4 = k4_tmap_1(sK2,sK3)
% 23.35/3.50      | sK4 != sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2250]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1,plain,
% 23.35/3.50      ( r1_tarski(X0,X0) ),
% 23.35/3.50      inference(cnf_transformation,[],[f85]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1790,plain,
% 23.35/3.50      ( r1_tarski(X0,X0) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_7918,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(u1_struct_0(sK3),k1_relat_1(k4_tmap_1(sK2,sK3))) = iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_1790,c_7908]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_8229,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(u1_struct_0(sK3),k1_relat_1(k4_tmap_1(sK2,sK3))) = iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_7918,c_512,c_519,c_2224,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_8235,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) = iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_5648,c_8229]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5661,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_5648,c_2914]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5672,plain,
% 23.35/3.50      ( k1_funct_1(sK4,X0) = X0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_5648,c_1774]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5739,plain,
% 23.35/3.50      ( k1_funct_1(sK4,X0) = X0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 23.35/3.50      inference(backward_subsumption_resolution,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_5661,c_5672]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_6758,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_1777,c_5739]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_9003,plain,
% 23.35/3.50      ( v1_relat_1(X0) != iProver_top
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_6758,c_41,c_43,c_2221,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_9004,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_9003]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_14233,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_8235,c_9004]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_9017,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),u1_struct_0(sK3)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_7699,c_9004]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_14224,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),u1_struct_0(sK3)) = iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_7699,c_8235]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_19603,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_14233,c_512,c_519,c_2224,c_2299,c_9017,c_14224]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_7707,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(X0),u1_struct_0(sK3)) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_7699,c_1775]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_8731,plain,
% 23.35/3.50      ( v1_relat_1(X0) != iProver_top
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(X0),u1_struct_0(sK3)) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_7707,c_512,c_519,c_2224,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_8732,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(X0),u1_struct_0(sK3)) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_8731]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_8742,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_1790,c_8732]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_8840,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_8742,c_512,c_519,c_2224,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_8847,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) = iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_5648,c_8840]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_17338,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_8847,c_10505]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_17647,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_17338,c_41,c_43,c_2221,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_17657,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_17647,c_1791]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_18059,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_17657,c_30,c_29,c_28,c_511,c_518,c_546,c_831,c_2122,
% 23.35/3.50                 c_2184,c_2608,c_5589]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_19621,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_19603,c_18059]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_19,plain,
% 23.35/3.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 23.35/3.50      | ~ r1_tarski(X1,X2)
% 23.35/3.50      | ~ v1_funct_1(X2)
% 23.35/3.50      | ~ v1_funct_1(X1)
% 23.35/3.50      | ~ v1_relat_1(X1)
% 23.35/3.50      | ~ v1_relat_1(X2)
% 23.35/3.50      | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
% 23.35/3.50      inference(cnf_transformation,[],[f67]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1776,plain,
% 23.35/3.50      ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
% 23.35/3.50      | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
% 23.35/3.50      | r1_tarski(X2,X0) != iProver_top
% 23.35/3.50      | v1_funct_1(X2) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X2) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_4258,plain,
% 23.35/3.50      ( k1_funct_1(X0,sK1(X1,X2)) = k1_funct_1(X1,sK1(X1,X2))
% 23.35/3.50      | r1_tarski(X1,X0) != iProver_top
% 23.35/3.50      | r1_tarski(X1,X2) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(X1),k1_relat_1(X2)) != iProver_top
% 23.35/3.50      | v1_funct_1(X2) != iProver_top
% 23.35/3.50      | v1_funct_1(X1) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X1) != iProver_top
% 23.35/3.50      | v1_relat_1(X2) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_1777,c_1776]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_10310,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(X1,sK1(k4_tmap_1(sK2,sK3),X0))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X1) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X1) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_7699,c_4258]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_15012,plain,
% 23.35/3.50      ( v1_relat_1(X1) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(X1,sK1(k4_tmap_1(sK2,sK3),X0))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X1) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_10310,c_512,c_519,c_2224,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_15013,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(X1,sK1(k4_tmap_1(sK2,sK3),X0))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X1) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_15012]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_17665,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0))
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(u1_struct_0(sK3),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_17647,c_15013]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_17,plain,
% 23.35/3.50      ( r1_tarski(X0,X1)
% 23.35/3.50      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 23.35/3.50      | ~ v1_funct_1(X1)
% 23.35/3.50      | ~ v1_funct_1(X0)
% 23.35/3.50      | ~ v1_relat_1(X0)
% 23.35/3.50      | ~ v1_relat_1(X1)
% 23.35/3.50      | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1)) ),
% 23.35/3.50      inference(cnf_transformation,[],[f69]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2609,plain,
% 23.35/3.50      ( r1_tarski(X0,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(k4_tmap_1(sK2,sK3)))
% 23.35/3.50      | ~ v1_funct_1(X0)
% 23.35/3.50      | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
% 23.35/3.50      | ~ v1_relat_1(X0)
% 23.35/3.50      | ~ v1_relat_1(k4_tmap_1(sK2,sK3))
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(X0,k4_tmap_1(sK2,sK3))) != k1_funct_1(X0,sK1(X0,k4_tmap_1(sK2,sK3))) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_17]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3754,plain,
% 23.35/3.50      ( ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3)))
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
% 23.35/3.50      | ~ v1_funct_1(sK4)
% 23.35/3.50      | ~ v1_relat_1(k4_tmap_1(sK2,sK3))
% 23.35/3.50      | ~ v1_relat_1(sK4)
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) != k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2609]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_3755,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) != k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_3754]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5663,plain,
% 23.35/3.50      ( k1_relset_1(k1_relat_1(sK4),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_5648,c_2533]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5665,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_5648,c_1769]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_6521,plain,
% 23.35/3.50      ( k1_relset_1(k1_relat_1(sK4),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | v1_funct_2(k4_tmap_1(sK2,sK3),k1_relat_1(sK4),u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_5665,c_1779]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5669,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | v1_funct_2(k4_tmap_1(sK2,sK3),k1_relat_1(sK4),u1_struct_0(sK2)) = iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_5648,c_1766]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_7211,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | k1_relset_1(k1_relat_1(sK4),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_6521,c_5787,c_6550]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_7212,plain,
% 23.35/3.50      ( k1_relset_1(k1_relat_1(sK4),u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_7211]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_8543,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4) ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_5663,c_7212]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_16043,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
% 23.35/3.50      | v1_funct_1(X1) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(X1) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_8543,c_1776]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_16878,plain,
% 23.35/3.50      ( v1_relat_1(X1) != iProver_top
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
% 23.35/3.50      | v1_funct_1(X1) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_16043,c_512,c_519,c_2224,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_16879,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(X1,X0)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X1) != iProver_top
% 23.35/3.50      | v1_funct_1(X1) != iProver_top
% 23.35/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_16878]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_17664,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_17647,c_16879]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_20329,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_17664,c_41,c_43,c_2221,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_20340,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_1777,c_20329]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_21563,plain,
% 23.35/3.50      ( v1_relat_1(X0) != iProver_top
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_20340,c_41,c_43,c_2221,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_21564,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = k1_funct_1(sK4,sK1(sK4,X0))
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_21563]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_21579,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3)))
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_8235,c_21564]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_21637,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_17665,c_30,c_41,c_29,c_28,c_43,c_511,c_512,c_518,
% 23.35/3.50                 c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,c_2299,
% 23.35/3.50                 c_2608,c_3755,c_5589,c_8235,c_17657,c_21579]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_53785,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_19621,c_30,c_29,c_28,c_116,c_120,c_511,c_518,c_546,
% 23.35/3.50                 c_831,c_2122,c_2184,c_2251,c_2414,c_2444,c_2513,c_3065,
% 23.35/3.50                 c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,
% 23.35/3.50                 c_11494,c_21637,c_43165,c_43179]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_25,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.35/3.50      | ~ r2_hidden(X2,u1_struct_0(X0))
% 23.35/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.35/3.50      | v2_struct_0(X1)
% 23.35/3.50      | v2_struct_0(X0)
% 23.35/3.50      | ~ v2_pre_topc(X1)
% 23.35/3.50      | ~ l1_pre_topc(X1)
% 23.35/3.50      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 23.35/3.50      inference(cnf_transformation,[],[f74]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_410,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.35/3.50      | ~ r2_hidden(X2,u1_struct_0(X0))
% 23.35/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.35/3.50      | v2_struct_0(X0)
% 23.35/3.50      | v2_struct_0(X1)
% 23.35/3.50      | ~ l1_pre_topc(X1)
% 23.35/3.50      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2
% 23.35/3.50      | sK2 != X1 ),
% 23.35/3.50      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_411,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,sK2)
% 23.35/3.50      | ~ r2_hidden(X1,u1_struct_0(X0))
% 23.35/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 23.35/3.50      | v2_struct_0(X0)
% 23.35/3.50      | v2_struct_0(sK2)
% 23.35/3.50      | ~ l1_pre_topc(sK2)
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,X0),X1) = X1 ),
% 23.35/3.50      inference(unflattening,[status(thm)],[c_410]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_415,plain,
% 23.35/3.50      ( ~ m1_pre_topc(X0,sK2)
% 23.35/3.50      | ~ r2_hidden(X1,u1_struct_0(X0))
% 23.35/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 23.35/3.50      | v2_struct_0(X0)
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,X0),X1) = X1 ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_411,c_35,c_33]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_524,plain,
% 23.35/3.50      ( ~ r2_hidden(X0,u1_struct_0(X1))
% 23.35/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 23.35/3.50      | v2_struct_0(X1)
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,X1),X0) = X0
% 23.35/3.50      | sK2 != sK2
% 23.35/3.50      | sK3 != X1 ),
% 23.35/3.50      inference(resolution_lifted,[status(thm)],[c_31,c_415]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_525,plain,
% 23.35/3.50      ( ~ r2_hidden(X0,u1_struct_0(sK3))
% 23.35/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 23.35/3.50      | v2_struct_0(sK3)
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
% 23.35/3.50      inference(unflattening,[status(thm)],[c_524]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_32,negated_conjecture,
% 23.35/3.50      ( ~ v2_struct_0(sK3) ),
% 23.35/3.50      inference(cnf_transformation,[],[f78]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_529,plain,
% 23.35/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 23.35/3.50      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_525,c_32]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_530,plain,
% 23.35/3.50      ( ~ r2_hidden(X0,u1_struct_0(sK3))
% 23.35/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0 ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_529]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1767,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
% 23.35/3.50      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
% 23.35/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_530]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5664,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_5648,c_1767]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5740,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 23.35/3.50      inference(backward_subsumption_resolution,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_5661,c_5664]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_8610,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_1777,c_5740]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_9526,plain,
% 23.35/3.50      ( v1_relat_1(X0) != iProver_top
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_8610,c_41,c_43,c_2221,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_9527,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_9526]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_9540,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),u1_struct_0(sK3)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_7699,c_9527]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_14232,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_8235,c_9527]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_20583,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_9540,c_512,c_519,c_2224,c_2299,c_14232]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_20584,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_20583]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_10467,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | m1_subset_1(sK1(k4_tmap_1(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_10452,c_1767]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_10506,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(backward_subsumption_resolution,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_10466,c_10467]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_17337,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_8847,c_10506]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_18407,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_17337,c_41,c_43,c_2221,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_18417,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_18407,c_1791]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_18555,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_18417,c_30,c_29,c_28,c_511,c_518,c_546,c_831,c_2122,
% 23.35/3.50                 c_2184,c_2608,c_5589]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_20601,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_20584,c_18555]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54012,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_20601,c_30,c_29,c_28,c_116,c_120,c_511,c_518,c_546,
% 23.35/3.50                 c_831,c_2122,c_2184,c_2251,c_2414,c_2444,c_2513,c_3065,
% 23.35/3.50                 c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,
% 23.35/3.50                 c_11494,c_43165,c_43179]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54013,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_54012]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1778,plain,
% 23.35/3.50      ( k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 23.35/3.50      | r1_tarski(X1,X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(X1) != iProver_top
% 23.35/3.50      | v1_relat_1(X1) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54017,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_54013,c_1778]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_20593,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_20584,c_1791]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54162,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_54017,c_30,c_41,c_29,c_28,c_43,c_116,c_120,c_511,
% 23.35/3.50                 c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,
% 23.35/3.50                 c_2224,c_2251,c_2299,c_2414,c_2444,c_2513,c_2608,c_3065,
% 23.35/3.50                 c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,
% 23.35/3.50                 c_8847,c_11494,c_20593,c_21637,c_43165,c_43179]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54163,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_54162]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54166,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_54163,c_30,c_41,c_29,c_28,c_43,c_116,c_120,c_511,
% 23.35/3.50                 c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,
% 23.35/3.50                 c_2224,c_2251,c_2299,c_2414,c_2444,c_2513,c_2608,c_3065,
% 23.35/3.50                 c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,
% 23.35/3.50                 c_8847,c_11494,c_20593,c_21637,c_43165,c_43179,c_54017]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54167,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_54166]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54170,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) != sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_54167,c_1778]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_19620,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_19603,c_18555]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_53789,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_19620,c_30,c_29,c_28,c_116,c_120,c_511,c_518,c_546,
% 23.35/3.50                 c_831,c_2122,c_2184,c_2251,c_2414,c_2444,c_2513,c_3065,
% 23.35/3.50                 c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,
% 23.35/3.50                 c_11494,c_43165,c_43179]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_53790,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_53789]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_53794,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_53790,c_1778]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_19613,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_19603,c_1791]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54153,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_53794,c_30,c_41,c_29,c_28,c_43,c_116,c_120,c_511,
% 23.35/3.50                 c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,
% 23.35/3.50                 c_2224,c_2251,c_2299,c_2414,c_2444,c_2513,c_2608,c_3065,
% 23.35/3.50                 c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,
% 23.35/3.50                 c_8847,c_11494,c_19613,c_21637,c_43165,c_43179]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54154,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_54153]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54157,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_54154,c_30,c_41,c_29,c_28,c_43,c_116,c_120,c_511,
% 23.35/3.50                 c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,
% 23.35/3.50                 c_2224,c_2251,c_2299,c_2414,c_2444,c_2513,c_2608,c_3065,
% 23.35/3.50                 c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,
% 23.35/3.50                 c_8847,c_11494,c_19613,c_21637,c_43165,c_43179,c_53794]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54158,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_54157]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54185,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_54170,c_30,c_41,c_29,c_28,c_43,c_116,c_120,c_511,
% 23.35/3.50                 c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,
% 23.35/3.50                 c_2224,c_2251,c_2299,c_2414,c_2444,c_2513,c_3065,c_3682,
% 23.35/3.50                 c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8235,c_8566,
% 23.35/3.50                 c_11494,c_43165,c_43179,c_54158]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54195,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_54185,c_1791]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_18424,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = k1_funct_1(sK4,X0)
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_18407,c_16879]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_58165,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_18424,c_30,c_29,c_28,c_116,c_120,c_511,c_518,c_546,
% 23.35/3.50                 c_831,c_2122,c_2184,c_2251,c_2414,c_2444,c_2513,c_3065,
% 23.35/3.50                 c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,
% 23.35/3.50                 c_11494,c_43165,c_43179,c_54215]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_58166,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_58165]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_58169,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_58166,c_1778]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54641,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | u1_struct_0(sK3) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) = iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_5648,c_54629]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_9091,plain,
% 23.35/3.50      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(X0))
% 23.35/3.50      | ~ r1_tarski(sK4,X0)
% 23.35/3.50      | ~ v1_funct_1(X0)
% 23.35/3.50      | ~ v1_funct_1(sK4)
% 23.35/3.50      | ~ v1_relat_1(X0)
% 23.35/3.50      | ~ v1_relat_1(sK4) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_20]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_9096,plain,
% 23.35/3.50      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) = iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_9091]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54821,plain,
% 23.35/3.50      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) = iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_54641,c_41,c_43,c_2221,c_2299,c_9096]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_54837,plain,
% 23.35/3.50      ( k1_relat_1(X0) = k1_relat_1(sK4)
% 23.35/3.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_54821,c_1791]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_55194,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4)
% 23.35/3.50      | r1_tarski(u1_struct_0(sK3),k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_7699,c_54837]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_42,plain,
% 23.35/3.50      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_547,plain,
% 23.35/3.50      ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_4997,plain,
% 23.35/3.50      ( k1_relat_1(sK4) = k1_relat_1(sK4) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1245]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5002,plain,
% 23.35/3.50      ( X0 != X1 | k1_relat_1(sK4) != X1 | k1_relat_1(sK4) = X0 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1246]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_10112,plain,
% 23.35/3.50      ( X0 != k1_relat_1(sK4)
% 23.35/3.50      | k1_relat_1(sK4) = X0
% 23.35/3.50      | k1_relat_1(sK4) != k1_relat_1(sK4) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_5002]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_18634,plain,
% 23.35/3.50      ( u1_struct_0(sK3) != k1_relat_1(sK4)
% 23.35/3.50      | k1_relat_1(sK4) = u1_struct_0(sK3)
% 23.35/3.50      | k1_relat_1(sK4) != k1_relat_1(sK4) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_10112]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_14575,plain,
% 23.35/3.50      ( X0 != X1
% 23.35/3.50      | k1_relat_1(k4_tmap_1(sK2,sK3)) != X1
% 23.35/3.50      | k1_relat_1(k4_tmap_1(sK2,sK3)) = X0 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1246]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_22509,plain,
% 23.35/3.50      ( X0 != u1_struct_0(sK3)
% 23.35/3.50      | k1_relat_1(k4_tmap_1(sK2,sK3)) = X0
% 23.35/3.50      | k1_relat_1(k4_tmap_1(sK2,sK3)) != u1_struct_0(sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_14575]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_34112,plain,
% 23.35/3.50      ( k1_relat_1(k4_tmap_1(sK2,sK3)) != u1_struct_0(sK3)
% 23.35/3.50      | k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4)
% 23.35/3.50      | k1_relat_1(sK4) != u1_struct_0(sK3) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_22509]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_55209,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_relat_1(sK4) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_55194,c_42,c_547,c_3614,c_3621,c_4997,c_18634,c_34112]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_55252,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK4)) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_55209,c_1775]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_56577,plain,
% 23.35/3.50      ( v1_relat_1(X0) != iProver_top
% 23.35/3.50      | u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK4)) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_55252,c_512,c_519,c_2224,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_56578,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK4)) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_56577]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_56588,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) = iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_1790,c_56578]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_58172,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = k1_xboole_0
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) = iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_56588,c_512,c_519,c_2224,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_58718,plain,
% 23.35/3.50      ( u1_struct_0(sK3) = k1_xboole_0 ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_54648,c_30,c_41,c_29,c_28,c_43,c_116,c_120,c_511,
% 23.35/3.50                 c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,
% 23.35/3.50                 c_2224,c_2251,c_2299,c_2414,c_2444,c_2513,c_2608,c_3065,
% 23.35/3.50                 c_3682,c_4102,c_4972,c_5589,c_5901,c_6153,c_6809,c_8566,
% 23.35/3.50                 c_11494,c_43165,c_43179,c_53785,c_54195,c_58169,c_58172]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_59018,plain,
% 23.35/3.50      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_relat_1(k4_tmap_1(sK2,sK3)) ),
% 23.35/3.50      inference(demodulation,[status(thm)],[c_58718,c_2533]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_59020,plain,
% 23.35/3.50      ( m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))) = iProver_top ),
% 23.35/3.50      inference(demodulation,[status(thm)],[c_58718,c_1769]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_12,plain,
% 23.35/3.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 23.35/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 23.35/3.50      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 23.35/3.50      inference(cnf_transformation,[],[f91]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_1780,plain,
% 23.35/3.50      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 23.35/3.50      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 23.35/3.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_61312,plain,
% 23.35/3.50      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_xboole_0
% 23.35/3.50      | v1_funct_2(k4_tmap_1(sK2,sK3),k1_xboole_0,u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_59020,c_1780]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2419,plain,
% 23.35/3.50      ( X0 != X1 | X0 = u1_struct_0(sK3) | u1_struct_0(sK3) != X1 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1246]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2420,plain,
% 23.35/3.50      ( u1_struct_0(sK3) != k1_xboole_0
% 23.35/3.50      | k1_xboole_0 = u1_struct_0(sK3)
% 23.35/3.50      | k1_xboole_0 != k1_xboole_0 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2419]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2507,plain,
% 23.35/3.50      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_1245]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2506,plain,
% 23.35/3.50      ( v1_funct_2(X0,X1,u1_struct_0(sK2))
% 23.35/3.50      | ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | X0 != k4_tmap_1(sK2,sK3)
% 23.35/3.50      | X1 != u1_struct_0(sK3)
% 23.35/3.50      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2135]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_16677,plain,
% 23.35/3.50      ( v1_funct_2(k4_tmap_1(sK2,sK3),X0,u1_struct_0(sK2))
% 23.35/3.50      | ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | X0 != u1_struct_0(sK3)
% 23.35/3.50      | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
% 23.35/3.50      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2506]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_16678,plain,
% 23.35/3.50      ( X0 != u1_struct_0(sK3)
% 23.35/3.50      | k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
% 23.35/3.50      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 23.35/3.50      | v1_funct_2(k4_tmap_1(sK2,sK3),X0,u1_struct_0(sK2)) = iProver_top
% 23.35/3.50      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_16677]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_16680,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) != k4_tmap_1(sK2,sK3)
% 23.35/3.50      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 23.35/3.50      | k1_xboole_0 != u1_struct_0(sK3)
% 23.35/3.50      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 23.35/3.50      | v1_funct_2(k4_tmap_1(sK2,sK3),k1_xboole_0,u1_struct_0(sK2)) = iProver_top ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_16678]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_61401,plain,
% 23.35/3.50      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK2),k4_tmap_1(sK2,sK3)) = k1_xboole_0 ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_61312,c_30,c_41,c_29,c_28,c_43,c_116,c_120,c_511,
% 23.35/3.50                 c_512,c_518,c_519,c_546,c_547,c_831,c_2122,c_2184,
% 23.35/3.50                 c_2221,c_2224,c_2251,c_2299,c_2414,c_2420,c_2444,c_2507,
% 23.35/3.50                 c_2513,c_2608,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,
% 23.35/3.50                 c_6153,c_6809,c_8566,c_11494,c_16680,c_43165,c_43179,
% 23.35/3.50                 c_53785,c_54195,c_58169,c_58172]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_62400,plain,
% 23.35/3.50      ( k1_relat_1(k4_tmap_1(sK2,sK3)) = k1_xboole_0 ),
% 23.35/3.50      inference(light_normalisation,[status(thm)],[c_59018,c_61401]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_62425,plain,
% 23.35/3.50      ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_xboole_0) = iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_62400,c_1777]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_62576,plain,
% 23.35/3.50      ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_xboole_0) = iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(light_normalisation,[status(thm)],[c_62425,c_62400]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_64099,plain,
% 23.35/3.50      ( v1_relat_1(X0) != iProver_top
% 23.35/3.50      | r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_xboole_0) = iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_62576,c_512,c_519,c_2224,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_64100,plain,
% 23.35/3.50      ( r2_hidden(sK1(k4_tmap_1(sK2,sK3),X0),k1_xboole_0) = iProver_top
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_64099]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_59015,plain,
% 23.35/3.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 23.35/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
% 23.35/3.50      inference(demodulation,[status(thm)],[c_58718,c_2914]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_59019,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
% 23.35/3.50      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 23.35/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(demodulation,[status(thm)],[c_58718,c_1767]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_59072,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),X0) = X0
% 23.35/3.50      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 23.35/3.50      inference(backward_subsumption_resolution,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_59015,c_59019]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_64111,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_64100,c_59072]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_59027,plain,
% 23.35/3.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))) = iProver_top ),
% 23.35/3.50      inference(demodulation,[status(thm)],[c_58718,c_1773]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_61040,plain,
% 23.35/3.50      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK2),sK4) = k1_xboole_0
% 23.35/3.50      | v1_funct_2(sK4,k1_xboole_0,u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_59027,c_1780]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2945,plain,
% 23.35/3.50      ( v1_funct_2(sK4,X0,u1_struct_0(sK2))
% 23.35/3.50      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
% 23.35/3.50      | X0 != u1_struct_0(sK3)
% 23.35/3.50      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 23.35/3.50      | sK4 != sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2312]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2946,plain,
% 23.35/3.50      ( X0 != u1_struct_0(sK3)
% 23.35/3.50      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 23.35/3.50      | sK4 != sK4
% 23.35/3.50      | v1_funct_2(sK4,X0,u1_struct_0(sK2)) = iProver_top
% 23.35/3.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_2945]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2948,plain,
% 23.35/3.50      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 23.35/3.50      | sK4 != sK4
% 23.35/3.50      | k1_xboole_0 != u1_struct_0(sK3)
% 23.35/3.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 23.35/3.50      | v1_funct_2(sK4,k1_xboole_0,u1_struct_0(sK2)) = iProver_top ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2946]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_61341,plain,
% 23.35/3.50      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK2),sK4) = k1_xboole_0 ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_61040,c_30,c_41,c_29,c_42,c_28,c_43,c_116,c_120,c_511,
% 23.35/3.50                 c_512,c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,
% 23.35/3.50                 c_2224,c_2251,c_2299,c_2414,c_2420,c_2444,c_2507,c_2513,
% 23.35/3.50                 c_2608,c_2948,c_3065,c_3682,c_4102,c_4972,c_5589,c_5901,
% 23.35/3.50                 c_6153,c_6809,c_8566,c_11494,c_43165,c_43179,c_53785,
% 23.35/3.50                 c_54195,c_58169,c_58172]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_59021,plain,
% 23.35/3.50      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK2),sK4) = k1_relat_1(sK4) ),
% 23.35/3.50      inference(demodulation,[status(thm)],[c_58718,c_2431]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_61344,plain,
% 23.35/3.50      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 23.35/3.50      inference(demodulation,[status(thm)],[c_61341,c_59021]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_62085,plain,
% 23.35/3.50      ( r2_hidden(sK1(sK4,X0),k1_xboole_0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_61344,c_1777]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_62236,plain,
% 23.35/3.50      ( r2_hidden(sK1(sK4,X0),k1_xboole_0) = iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(light_normalisation,[status(thm)],[c_62085,c_61344]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_63664,plain,
% 23.35/3.50      ( v1_relat_1(X0) != iProver_top
% 23.35/3.50      | r2_hidden(sK1(sK4,X0),k1_xboole_0) = iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_62236,c_41,c_43,c_2221,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_63665,plain,
% 23.35/3.50      ( r2_hidden(sK1(sK4,X0),k1_xboole_0) = iProver_top
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_63664]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_63676,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,X0)) = sK1(sK4,X0)
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_63665,c_59072]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_64899,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_62400,c_63676]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_115,plain,
% 23.35/3.50      ( r1_tarski(X0,X0) = iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_117,plain,
% 23.35/3.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_115]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72229,plain,
% 23.35/3.50      ( r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_64899,c_117,c_512,c_519,c_2224,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72230,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_72229]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72239,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_72230,c_1791]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_2150,plain,
% 23.35/3.50      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_0]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5499,plain,
% 23.35/3.50      ( ~ r1_tarski(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | ~ r1_tarski(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | k4_tmap_1(sK2,sK3) = sK4 ),
% 23.35/3.50      inference(instantiation,[status(thm)],[c_2150]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_5500,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(predicate_to_equality,[status(thm)],[c_5499]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_64978,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = X0
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_64111,c_1791]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72244,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_72230,c_64978]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72324,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(light_normalisation,[status(thm)],[c_72244,c_61344]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72419,plain,
% 23.35/3.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 23.35/3.50      | ~ v1_funct_1(sK4)
% 23.35/3.50      | ~ v1_relat_1(sK4)
% 23.35/3.50      | k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
% 23.35/3.50      inference(predicate_to_equality_rev,[status(thm)],[c_72324]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72608,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_72324,c_30,c_41,c_29,c_28,c_43,c_117,c_511,c_518,
% 23.35/3.50                 c_546,c_831,c_2122,c_2184,c_2221,c_2299,c_2608,c_5589]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72609,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_72608]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72612,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_72609,c_1778]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72613,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(light_normalisation,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_72612,c_61344,c_62400]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_59026,plain,
% 23.35/3.50      ( k1_funct_1(sK4,X0) = X0
% 23.35/3.50      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 23.35/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 23.35/3.50      inference(demodulation,[status(thm)],[c_58718,c_1774]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_59071,plain,
% 23.35/3.50      ( k1_funct_1(sK4,X0) = X0
% 23.35/3.50      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 23.35/3.50      inference(backward_subsumption_resolution,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_59015,c_59026]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_64112,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_64100,c_59071]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_64281,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = X0
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),X0)) = sK1(k4_tmap_1(sK2,sK3),X0)
% 23.35/3.50      | r1_tarski(X0,k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_64112,c_1791]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72245,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_72230,c_64281]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72311,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(light_normalisation,[status(thm)],[c_72245,c_61344]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72763,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_72613,c_30,c_41,c_29,c_28,c_43,c_117,c_511,c_512,
% 23.35/3.50                 c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,
% 23.35/3.50                 c_2299,c_2608,c_5589,c_72239,c_72311]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72766,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) != sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(k1_relat_1(sK4),k1_relat_1(k4_tmap_1(sK2,sK3))) != iProver_top
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_72763,c_1778]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_63677,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,X0)) = sK1(sK4,X0)
% 23.35/3.50      | r1_tarski(sK4,X0) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 23.35/3.50      | v1_funct_1(X0) != iProver_top
% 23.35/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_63665,c_59071]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_63856,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_62400,c_63677]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_65420,plain,
% 23.35/3.50      ( r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_63856,c_117,c_512,c_519,c_2224,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_65421,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_65420]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_65428,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_65421,c_1791]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_65430,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_65421,c_64281]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_65490,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(light_normalisation,[status(thm)],[c_65430,c_61344]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_65429,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_65421,c_64978]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_65503,plain,
% 23.35/3.50      ( k4_tmap_1(sK2,sK3) = sK4
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(light_normalisation,[status(thm)],[c_65429,c_61344]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_65987,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_65503,c_30,c_41,c_29,c_28,c_43,c_117,c_511,c_518,
% 23.35/3.50                 c_546,c_831,c_2122,c_2184,c_2221,c_2299,c_2608,c_5589]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_65988,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
% 23.35/3.50      inference(renaming,[status(thm)],[c_65987]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_65991,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_65988,c_1778]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_65992,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(light_normalisation,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_65991,c_61344,c_62400]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_66001,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(sK4,k4_tmap_1(sK2,sK3))) = sK1(sK4,k4_tmap_1(sK2,sK3)) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_65428,c_30,c_41,c_29,c_28,c_43,c_117,c_511,c_512,
% 23.35/3.50                 c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,
% 23.35/3.50                 c_2299,c_2608,c_5589,c_65490,c_65992]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72767,plain,
% 23.35/3.50      ( sK1(sK4,k4_tmap_1(sK2,sK3)) != sK1(sK4,k4_tmap_1(sK2,sK3))
% 23.35/3.50      | r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(light_normalisation,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_72766,c_61344,c_62400,c_66001]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72768,plain,
% 23.35/3.50      ( r1_tarski(sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(equality_resolution_simp,[status(thm)],[c_72767]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72779,plain,
% 23.35/3.50      ( r1_tarski(k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_72239,c_30,c_41,c_29,c_28,c_43,c_117,c_511,c_512,
% 23.35/3.50                 c_518,c_519,c_546,c_831,c_2122,c_2184,c_2221,c_2224,
% 23.35/3.50                 c_2299,c_2608,c_5500,c_5589,c_72768]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72788,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_64111,c_72779]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72814,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(light_normalisation,[status(thm)],[c_72788,c_61344]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_73124,plain,
% 23.35/3.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_72814,c_41,c_43,c_117,c_2221,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_73201,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) != sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 23.35/3.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK2,sK3)),k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_73124,c_1778]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72789,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(superposition,[status(thm)],[c_64112,c_72779]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_72805,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(light_normalisation,[status(thm)],[c_72789,c_61344]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_73012,plain,
% 23.35/3.50      ( k1_funct_1(sK4,sK1(k4_tmap_1(sK2,sK3),sK4)) = sK1(k4_tmap_1(sK2,sK3),sK4) ),
% 23.35/3.50      inference(global_propositional_subsumption,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_72805,c_41,c_43,c_117,c_2221,c_2299]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_73202,plain,
% 23.35/3.50      ( sK1(k4_tmap_1(sK2,sK3),sK4) != sK1(k4_tmap_1(sK2,sK3),sK4)
% 23.35/3.50      | r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(light_normalisation,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_73201,c_61344,c_62400,c_73012]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(c_73203,plain,
% 23.35/3.50      ( r1_tarski(k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 23.35/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.35/3.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_funct_1(sK4) != iProver_top
% 23.35/3.50      | v1_relat_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 23.35/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.35/3.50      inference(equality_resolution_simp,[status(thm)],[c_73202]) ).
% 23.35/3.50  
% 23.35/3.50  cnf(contradiction,plain,
% 23.35/3.50      ( $false ),
% 23.35/3.50      inference(minisat,
% 23.35/3.50                [status(thm)],
% 23.35/3.50                [c_73203,c_72768,c_5589,c_5500,c_2608,c_2299,c_2224,
% 23.35/3.50                 c_2221,c_2184,c_2122,c_831,c_546,c_519,c_518,c_512,
% 23.35/3.50                 c_511,c_117,c_43,c_28,c_29,c_41,c_30]) ).
% 23.35/3.50  
% 23.35/3.50  
% 23.35/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.35/3.50  
% 23.35/3.50  ------                               Statistics
% 23.35/3.50  
% 23.35/3.50  ------ General
% 23.35/3.50  
% 23.35/3.50  abstr_ref_over_cycles:                  0
% 23.35/3.50  abstr_ref_under_cycles:                 0
% 23.35/3.50  gc_basic_clause_elim:                   0
% 23.35/3.50  forced_gc_time:                         0
% 23.35/3.50  parsing_time:                           0.018
% 23.35/3.50  unif_index_cands_time:                  0.
% 23.35/3.50  unif_index_add_time:                    0.
% 23.35/3.50  orderings_time:                         0.
% 23.35/3.50  out_proof_time:                         0.047
% 23.35/3.50  total_time:                             2.832
% 23.35/3.50  num_of_symbols:                         55
% 23.35/3.50  num_of_terms:                           18962
% 23.35/3.50  
% 23.35/3.50  ------ Preprocessing
% 23.35/3.50  
% 23.35/3.50  num_of_splits:                          0
% 23.35/3.50  num_of_split_atoms:                     0
% 23.35/3.50  num_of_reused_defs:                     0
% 23.35/3.50  num_eq_ax_congr_red:                    18
% 23.35/3.50  num_of_sem_filtered_clauses:            1
% 23.35/3.50  num_of_subtypes:                        0
% 23.35/3.50  monotx_restored_types:                  0
% 23.35/3.50  sat_num_of_epr_types:                   0
% 23.35/3.50  sat_num_of_non_cyclic_types:            0
% 23.35/3.50  sat_guarded_non_collapsed_types:        0
% 23.35/3.50  num_pure_diseq_elim:                    0
% 23.35/3.50  simp_replaced_by:                       0
% 23.35/3.50  res_preprocessed:                       156
% 23.35/3.50  prep_upred:                             0
% 23.35/3.50  prep_unflattend:                        32
% 23.35/3.50  smt_new_axioms:                         0
% 23.35/3.50  pred_elim_cands:                        6
% 23.35/3.50  pred_elim:                              5
% 23.35/3.50  pred_elim_cl:                           5
% 23.35/3.50  pred_elim_cycles:                       8
% 23.35/3.50  merged_defs:                            0
% 23.35/3.50  merged_defs_ncl:                        0
% 23.35/3.50  bin_hyper_res:                          0
% 23.35/3.50  prep_cycles:                            4
% 23.35/3.50  pred_elim_time:                         0.009
% 23.35/3.50  splitting_time:                         0.
% 23.35/3.50  sem_filter_time:                        0.
% 23.35/3.50  monotx_time:                            0.
% 23.35/3.50  subtype_inf_time:                       0.
% 23.35/3.50  
% 23.35/3.50  ------ Problem properties
% 23.35/3.50  
% 23.35/3.50  clauses:                                30
% 23.35/3.50  conjectures:                            4
% 23.35/3.50  epr:                                    4
% 23.35/3.50  horn:                                   24
% 23.35/3.50  ground:                                 9
% 23.35/3.50  unary:                                  11
% 23.35/3.50  binary:                                 2
% 23.35/3.50  lits:                                   96
% 23.35/3.50  lits_eq:                                19
% 23.35/3.50  fd_pure:                                0
% 23.35/3.50  fd_pseudo:                              0
% 23.35/3.50  fd_cond:                                3
% 23.35/3.50  fd_pseudo_cond:                         1
% 23.35/3.50  ac_symbols:                             0
% 23.35/3.50  
% 23.35/3.50  ------ Propositional Solver
% 23.35/3.50  
% 23.35/3.50  prop_solver_calls:                      36
% 23.35/3.50  prop_fast_solver_calls:                 8405
% 23.35/3.50  smt_solver_calls:                       0
% 23.35/3.50  smt_fast_solver_calls:                  0
% 23.35/3.50  prop_num_of_clauses:                    13438
% 23.35/3.50  prop_preprocess_simplified:             19416
% 23.35/3.50  prop_fo_subsumed:                       1365
% 23.35/3.50  prop_solver_time:                       0.
% 23.35/3.50  smt_solver_time:                        0.
% 23.35/3.50  smt_fast_solver_time:                   0.
% 23.35/3.50  prop_fast_solver_time:                  0.
% 23.35/3.50  prop_unsat_core_time:                   0.001
% 23.35/3.50  
% 23.35/3.50  ------ QBF
% 23.35/3.50  
% 23.35/3.50  qbf_q_res:                              0
% 23.35/3.50  qbf_num_tautologies:                    0
% 23.35/3.50  qbf_prep_cycles:                        0
% 23.35/3.50  
% 23.35/3.50  ------ BMC1
% 23.35/3.50  
% 23.35/3.50  bmc1_current_bound:                     -1
% 23.35/3.50  bmc1_last_solved_bound:                 -1
% 23.35/3.50  bmc1_unsat_core_size:                   -1
% 23.35/3.50  bmc1_unsat_core_parents_size:           -1
% 23.35/3.50  bmc1_merge_next_fun:                    0
% 23.35/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.35/3.50  
% 23.35/3.50  ------ Instantiation
% 23.35/3.50  
% 23.35/3.50  inst_num_of_clauses:                    3351
% 23.35/3.50  inst_num_in_passive:                    1206
% 23.35/3.50  inst_num_in_active:                     1960
% 23.35/3.50  inst_num_in_unprocessed:                185
% 23.35/3.50  inst_num_of_loops:                      2570
% 23.35/3.50  inst_num_of_learning_restarts:          0
% 23.35/3.50  inst_num_moves_active_passive:          602
% 23.35/3.50  inst_lit_activity:                      0
% 23.35/3.50  inst_lit_activity_moves:                0
% 23.35/3.50  inst_num_tautologies:                   0
% 23.35/3.50  inst_num_prop_implied:                  0
% 23.35/3.50  inst_num_existing_simplified:           0
% 23.35/3.50  inst_num_eq_res_simplified:             0
% 23.35/3.50  inst_num_child_elim:                    0
% 23.35/3.50  inst_num_of_dismatching_blockings:      1661
% 23.35/3.50  inst_num_of_non_proper_insts:           5498
% 23.35/3.50  inst_num_of_duplicates:                 0
% 23.35/3.50  inst_inst_num_from_inst_to_res:         0
% 23.35/3.50  inst_dismatching_checking_time:         0.
% 23.35/3.50  
% 23.35/3.50  ------ Resolution
% 23.35/3.50  
% 23.35/3.50  res_num_of_clauses:                     0
% 23.35/3.50  res_num_in_passive:                     0
% 23.35/3.50  res_num_in_active:                      0
% 23.35/3.50  res_num_of_loops:                       160
% 23.35/3.50  res_forward_subset_subsumed:            495
% 23.35/3.50  res_backward_subset_subsumed:           4
% 23.35/3.50  res_forward_subsumed:                   0
% 23.35/3.50  res_backward_subsumed:                  0
% 23.35/3.50  res_forward_subsumption_resolution:     0
% 23.35/3.50  res_backward_subsumption_resolution:    0
% 23.35/3.50  res_clause_to_clause_subsumption:       22341
% 23.35/3.50  res_orphan_elimination:                 0
% 23.35/3.50  res_tautology_del:                      395
% 23.35/3.50  res_num_eq_res_simplified:              0
% 23.35/3.50  res_num_sel_changes:                    0
% 23.35/3.50  res_moves_from_active_to_pass:          0
% 23.35/3.50  
% 23.35/3.50  ------ Superposition
% 23.35/3.50  
% 23.35/3.50  sup_time_total:                         0.
% 23.35/3.50  sup_time_generating:                    0.
% 23.35/3.50  sup_time_sim_full:                      0.
% 23.35/3.50  sup_time_sim_immed:                     0.
% 23.35/3.50  
% 23.35/3.50  sup_num_of_clauses:                     795
% 23.35/3.50  sup_num_in_active:                      116
% 23.35/3.50  sup_num_in_passive:                     679
% 23.35/3.50  sup_num_of_loops:                       512
% 23.35/3.50  sup_fw_superposition:                   1366
% 23.35/3.50  sup_bw_superposition:                   1373
% 23.35/3.50  sup_immediate_simplified:               737
% 23.35/3.50  sup_given_eliminated:                   0
% 23.35/3.50  comparisons_done:                       0
% 23.35/3.50  comparisons_avoided:                    1663
% 23.35/3.50  
% 23.35/3.50  ------ Simplifications
% 23.35/3.50  
% 23.35/3.50  
% 23.35/3.50  sim_fw_subset_subsumed:                 288
% 23.35/3.50  sim_bw_subset_subsumed:                 94
% 23.35/3.50  sim_fw_subsumed:                        302
% 23.35/3.50  sim_bw_subsumed:                        16
% 23.35/3.50  sim_fw_subsumption_res:                 4
% 23.35/3.50  sim_bw_subsumption_res:                 8
% 23.35/3.50  sim_tautology_del:                      39
% 23.35/3.50  sim_eq_tautology_del:                   639
% 23.35/3.50  sim_eq_res_simp:                        3
% 23.35/3.50  sim_fw_demodulated:                     1
% 23.35/3.50  sim_bw_demodulated:                     337
% 23.35/3.50  sim_light_normalised:                   182
% 23.35/3.50  sim_joinable_taut:                      0
% 23.35/3.50  sim_joinable_simp:                      0
% 23.35/3.50  sim_ac_normalised:                      0
% 23.35/3.50  sim_smt_subsumption:                    0
% 23.35/3.50  
%------------------------------------------------------------------------------
