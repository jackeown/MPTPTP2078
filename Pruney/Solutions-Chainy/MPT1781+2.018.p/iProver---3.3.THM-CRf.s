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
% DateTime   : Thu Dec  3 12:23:47 EST 2020

% Result     : Theorem 7.36s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_5338)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
                & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f42,plain,(
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
     => ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3)
        & ! [X3] :
            ( k1_funct_1(sK3,X3) = X3
            | ~ r2_hidden(X3,u1_struct_0(X1))
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2)
            & ! [X3] :
                ( k1_funct_1(X2,X3) = X3
                | ~ r2_hidden(X3,u1_struct_0(sK2))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
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
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    & ! [X3] :
        ( k1_funct_1(sK3,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK2))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f42,f41,f40])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f58])).

fof(f77,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1530,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1528,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1534,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1878,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1528,c_1534])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_802,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK2) != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_803,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3) = u1_struct_0(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_805,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3) = u1_struct_0(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_803,c_26])).

cnf(c_1968,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_1878,c_805])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_740,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | u1_struct_0(sK1) != k1_xboole_0
    | u1_struct_0(sK2) != X1
    | sK3 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_741,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK2)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_740])).

cnf(c_1522,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK2)
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_2177,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1968,c_1522])).

cnf(c_13,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_24,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_371,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k4_tmap_1(sK1,sK2) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_372,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | sK3 != k4_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_455,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_32])).

cnf(c_456,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_subset_1(k4_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_460,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_subset_1(k4_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_33,c_31])).

cnf(c_510,plain,
    ( m1_subset_1(k4_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_460])).

cnf(c_511,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_437,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_438,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k4_tmap_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_442,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | v1_funct_1(k4_tmap_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_33,c_31])).

cnf(c_517,plain,
    ( v1_funct_1(k4_tmap_1(sK1,X0))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_442])).

cnf(c_518,plain,
    ( v1_funct_1(k4_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_20,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_392,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_393,plain,
    ( v1_funct_2(k4_tmap_1(sK1,X0),u1_struct_0(X0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_397,plain,
    ( v1_funct_2(k4_tmap_1(sK1,X0),u1_struct_0(X0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_33,c_31])).

cnf(c_545,plain,
    ( v1_funct_2(k4_tmap_1(sK1,X0),u1_struct_0(X0),u1_struct_0(sK1))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_397])).

cnf(c_546,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_1148,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1591,plain,
    ( k4_tmap_1(sK1,sK2) != X0
    | sK3 != X0
    | sK3 = k4_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_1592,plain,
    ( k4_tmap_1(sK1,sK2) != k1_xboole_0
    | sK3 = k4_tmap_1(sK1,sK2)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_1525,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_2119,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1968,c_1525])).

cnf(c_2121,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1968,c_1528])).

cnf(c_756,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k4_tmap_1(sK1,sK2) != X0
    | u1_struct_0(sK1) != k1_xboole_0
    | u1_struct_0(sK2) != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_546])).

cnf(c_757,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = k4_tmap_1(sK1,sK2)
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_756])).

cnf(c_1521,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = k4_tmap_1(sK1,sK2)
    | k1_xboole_0 = u1_struct_0(sK2)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_2221,plain,
    ( k4_tmap_1(sK1,sK2) = k1_xboole_0
    | u1_struct_0(sK2) = k1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1968,c_1521])).

cnf(c_3249,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2177,c_372,c_511,c_518,c_546,c_1592,c_2119,c_2121,c_2221])).

cnf(c_1879,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_relat_1(k4_tmap_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1525,c_1534])).

cnf(c_813,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k4_tmap_1(sK1,sK2) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK2) != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_546])).

cnf(c_814,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = u1_struct_0(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_813])).

cnf(c_816,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = u1_struct_0(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_814,c_511])).

cnf(c_2181,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_1879,c_816])).

cnf(c_16,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1532,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_410,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_411,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ r2_hidden(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_funct_1(k4_tmap_1(sK1,X0),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_415,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ r2_hidden(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(X0)
    | k1_funct_1(k4_tmap_1(sK1,X0),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_33,c_31])).

cnf(c_524,plain,
    ( ~ r2_hidden(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(X1)
    | k1_funct_1(k4_tmap_1(sK1,X1),X0) = X0
    | sK1 != sK1
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_415])).

cnf(c_525,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_529,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,u1_struct_0(sK2))
    | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_525,c_30])).

cnf(c_530,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
    inference(renaming,[status(thm)],[c_529])).

cnf(c_1523,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_3265,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_1523])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_488,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_489,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_503,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_489])).

cnf(c_504,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_1526,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1537,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2275,plain,
    ( r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_1537])).

cnf(c_3259,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_2275])).

cnf(c_3734,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3265,c_3259])).

cnf(c_3735,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3734])).

cnf(c_3740,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1532,c_3735])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1535,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1536,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2264,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1528,c_1536])).

cnf(c_2517,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_2264])).

cnf(c_4419,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3740,c_39,c_2517])).

cnf(c_4420,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4419])).

cnf(c_4427,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2181,c_4420])).

cnf(c_519,plain,
    ( v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_2265,plain,
    ( v1_relat_1(k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_1536])).

cnf(c_2672,plain,
    ( v1_relat_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_2265])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1538,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2743,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2181,c_1530])).

cnf(c_4058,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2743,c_519,c_2672])).

cnf(c_4059,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4058])).

cnf(c_4064,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_4059])).

cnf(c_4627,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4064,c_519,c_2672])).

cnf(c_4631,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_4627])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_108,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_112,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1584,plain,
    ( u1_struct_0(sK2) != X0
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_1648,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_1147,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1672,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_1840,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_1704,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_1941,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1704])).

cnf(c_1942,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1941])).

cnf(c_2031,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_2032,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_1150,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2133,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_2688,plain,
    ( ~ m1_subset_1(sK3,X0)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2133])).

cnf(c_3015,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2688])).

cnf(c_3239,plain,
    ( k4_tmap_1(sK1,sK2) = k4_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_2194,plain,
    ( X0 != X1
    | k4_tmap_1(sK1,sK2) != X1
    | k4_tmap_1(sK1,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_3338,plain,
    ( X0 != k4_tmap_1(sK1,sK2)
    | k4_tmap_1(sK1,sK2) = X0
    | k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2194])).

cnf(c_3339,plain,
    ( k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2)
    | k4_tmap_1(sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != k4_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3338])).

cnf(c_1151,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_4026,plain,
    ( k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1151])).

cnf(c_2143,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | k4_tmap_1(sK1,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != X1 ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_2800,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),X0)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != X0 ),
    inference(instantiation,[status(thm)],[c_2143])).

cnf(c_4762,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
    | k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2800])).

cnf(c_1154,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_5244,plain,
    ( k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | k1_xboole_0 != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1154])).

cnf(c_5270,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4631,c_26,c_108,c_112,c_372,c_511,c_518,c_546,c_741,c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,c_3015,c_3239,c_3339,c_4026,c_4762,c_5244])).

cnf(c_5278,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5270,c_4420])).

cnf(c_7144,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4427,c_26,c_108,c_112,c_372,c_511,c_518,c_519,c_546,c_741,c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,c_2672,c_3015,c_3239,c_3339,c_4026,c_4762,c_5244,c_5338])).

cnf(c_7145,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7144])).

cnf(c_2744,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2181,c_1530])).

cnf(c_4316,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2744,c_519,c_2672])).

cnf(c_4317,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4316])).

cnf(c_4322,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_4317])).

cnf(c_4638,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4322,c_519,c_2672])).

cnf(c_4643,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_4638])).

cnf(c_5347,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4643,c_26,c_108,c_112,c_372,c_511,c_518,c_546,c_741,c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,c_3015,c_3239,c_3339,c_4026,c_4762,c_5244])).

cnf(c_2832,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2181,c_1532])).

cnf(c_4555,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK1) = k1_xboole_0
    | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2832,c_519,c_2672])).

cnf(c_4556,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4555])).

cnf(c_4564,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | m1_subset_1(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4556,c_1523])).

cnf(c_4563,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | m1_subset_1(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK1)) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4556,c_2275])).

cnf(c_5256,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4564,c_4563])).

cnf(c_5257,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5256])).

cnf(c_5355,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5347,c_5257])).

cnf(c_5999,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5355,c_39,c_26,c_108,c_112,c_372,c_511,c_518,c_546,c_741,c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,c_2517,c_3015,c_3239,c_3339,c_4026,c_4762,c_5244])).

cnf(c_1539,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6004,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5999,c_1539])).

cnf(c_1703,plain,
    ( k4_tmap_1(sK1,sK2) != sK3
    | sK3 = k4_tmap_1(sK1,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_6312,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6004,c_372,c_511,c_518,c_546,c_1703,c_1840])).

cnf(c_7151,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7145,c_6312])).

cnf(c_15,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1533,plain,
    ( k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | r1_tarski(X1,X0) = iProver_top
    | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9863,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7151,c_1533])).

cnf(c_7150,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7145,c_1539])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k1_funct_1(sK3,X0) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1529,plain,
    ( k1_funct_1(sK3,X0) = X0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4565,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | m1_subset_1(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4556,c_1529])).

cnf(c_5104,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4565,c_4563])).

cnf(c_5105,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5104])).

cnf(c_5356,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5347,c_5105])).

cnf(c_5484,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5356,c_39,c_26,c_108,c_112,c_372,c_511,c_518,c_546,c_741,c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,c_2517,c_3015,c_3239,c_3339,c_4026,c_4762,c_5244])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_tarski(X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1531,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2833,plain,
    ( k1_funct_1(X0,sK0(X1,X2)) = k1_funct_1(X1,sK0(X1,X2))
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k1_relat_1(X1),k1_relat_1(X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1532,c_1531])).

cnf(c_5570,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(X1,sK0(k4_tmap_1(sK1,sK2),X0))
    | u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2181,c_2833])).

cnf(c_7514,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(X1,sK0(k4_tmap_1(sK1,sK2),X0))
    | u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5570,c_519,c_2672])).

cnf(c_7515,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(X1,sK0(k4_tmap_1(sK1,sK2),X0))
    | u1_struct_0(sK1) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7514])).

cnf(c_7520,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5484,c_7515])).

cnf(c_7532,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7520,c_39,c_26,c_108,c_112,c_372,c_511,c_518,c_546,c_741,c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,c_2517,c_3015,c_3239,c_3339,c_4026,c_4762,c_5244])).

cnf(c_7533,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7532])).

cnf(c_7540,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_7533])).

cnf(c_5489,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5484,c_1539])).

cnf(c_3034,plain,
    ( r1_tarski(X0,k4_tmap_1(sK1,sK2))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(k4_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0,k4_tmap_1(sK1,sK2))) != k1_funct_1(X0,sK0(X0,k4_tmap_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_6876,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2)))
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_3034])).

cnf(c_6877,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2)))
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) != iProver_top
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6876])).

cnf(c_2742,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(X1,X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2181,c_1531])).

cnf(c_3858,plain,
    ( v1_relat_1(X1) != iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(X1,X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2742,c_519,c_2672])).

cnf(c_3859,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(X1,X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3858])).

cnf(c_5492,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5484,c_3859])).

cnf(c_6667,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5492,c_39,c_26,c_108,c_112,c_372,c_511,c_518,c_546,c_741,c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,c_2517,c_3015,c_3239,c_3339,c_4026,c_4762,c_5244])).

cnf(c_6668,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6667])).

cnf(c_6674,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_6668])).

cnf(c_6682,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1532,c_6674])).

cnf(c_7864,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6682,c_39,c_2517])).

cnf(c_7865,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7864])).

cnf(c_7872,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2)))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5270,c_7865])).

cnf(c_8150,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7540,c_39,c_372,c_511,c_518,c_519,c_546,c_1703,c_1840,c_2517,c_2672,c_5270,c_5489,c_6877,c_7872])).

cnf(c_10022,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9863,c_39,c_372,c_511,c_518,c_519,c_546,c_1703,c_1840,c_2517,c_2672,c_5347,c_7150,c_8150])).

cnf(c_10024,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) != sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) != iProver_top
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10022,c_1533])).

cnf(c_3270,plain,
    ( k1_funct_1(sK3,X0) = X0
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_1529])).

cnf(c_3441,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_funct_1(sK3,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3270,c_3259])).

cnf(c_3442,plain,
    ( k1_funct_1(sK3,X0) = X0
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3441])).

cnf(c_3447,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1532,c_3442])).

cnf(c_3847,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3447,c_39,c_2517])).

cnf(c_3848,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3847])).

cnf(c_5279,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5270,c_3848])).

cnf(c_5870,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5279,c_519,c_2672])).

cnf(c_5875,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5870,c_1539])).

cnf(c_6305,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5875,c_372,c_511,c_518,c_546,c_1703,c_1840])).

cnf(c_6309,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5999,c_6305])).

cnf(c_8461,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6309,c_1533])).

cnf(c_2519,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2517])).

cnf(c_2674,plain,
    ( v1_relat_1(k4_tmap_1(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2672])).

cnf(c_5349,plain,
    ( r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3))
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5347])).

cnf(c_5878,plain,
    ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
    | k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5875])).

cnf(c_8462,plain,
    ( r1_tarski(k4_tmap_1(sK1,sK2),sK3)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8461])).

cnf(c_8730,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8461,c_28,c_372,c_511,c_518,c_546,c_1703,c_1840,c_2519,c_2674,c_5349,c_5878,c_8150,c_8462])).

cnf(c_10027,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10024,c_39,c_519,c_2517,c_2672,c_5270,c_8730])).

cnf(c_4561,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_4556])).

cnf(c_5276,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5270,c_1539])).

cnf(c_5353,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5347,c_1539])).

cnf(c_5583,plain,
    ( k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5276,c_5270,c_5353])).

cnf(c_5584,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_5583])).

cnf(c_5594,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5584,c_1532])).

cnf(c_6118,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4561,c_519,c_2672,c_5594])).

cnf(c_6124,plain,
    ( k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),X1)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X1))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X1)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6118,c_1531])).

cnf(c_9238,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),X1)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X1))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X1)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6124,c_39,c_2517])).

cnf(c_9239,plain,
    ( k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),X1)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X1))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X1)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9238])).

cnf(c_9248,plain,
    ( k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),X1)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X1))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X1)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2181,c_9239])).

cnf(c_9606,plain,
    ( k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),X1)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X1))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X1)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9248,c_26,c_108,c_112,c_372,c_511,c_518,c_546,c_741,c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,c_3015,c_3239,c_3339,c_4026,c_4762,c_5244])).

cnf(c_9607,plain,
    ( k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),X1)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X1))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X1)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9606])).

cnf(c_10037,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10027,c_9607])).

cnf(c_13728,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10037,c_519,c_2672])).

cnf(c_13729,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13728])).

cnf(c_13739,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_13729])).

cnf(c_13749,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_13739])).

cnf(c_10035,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10027,c_1539])).

cnf(c_10046,plain,
    ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
    | k4_tmap_1(sK1,sK2) = sK3
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10035])).

cnf(c_5351,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2181,c_5347])).

cnf(c_5499,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5351,c_26,c_108,c_112,c_372,c_511,c_518,c_546,c_741,c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,c_3015,c_3239,c_3339,c_4026,c_4762,c_5244])).

cnf(c_13738,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5499,c_13729])).

cnf(c_9246,plain,
    ( k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5347,c_9239])).

cnf(c_12556,plain,
    ( v1_relat_1(X0) != iProver_top
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3))
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9246,c_39,c_372,c_511,c_518,c_546,c_1703,c_1840,c_2517,c_10035])).

cnf(c_12557,plain,
    ( k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12556])).

cnf(c_12563,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3))
    | u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10027,c_12557])).

cnf(c_13949,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13738,c_519,c_2672,c_12563])).

cnf(c_13950,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3))
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_13949])).

cnf(c_13951,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13950,c_1533])).

cnf(c_13952,plain,
    ( r1_tarski(k4_tmap_1(sK1,sK2),sK3)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
    | ~ v1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13951])).

cnf(c_13954,plain,
    ( u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13749,c_28,c_372,c_511,c_518,c_546,c_1703,c_1840,c_2519,c_2674,c_5349,c_10046,c_13952])).

cnf(c_14039,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_relat_1(k4_tmap_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_13954,c_1879])).

cnf(c_14046,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13954,c_816])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_789,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k4_tmap_1(sK1,sK2) != X0
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK2) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_546])).

cnf(c_790,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0
    | u1_struct_0(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_789])).

cnf(c_791,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0
    | u1_struct_0(sK2) != k1_xboole_0
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_14047,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13954,c_1525])).

cnf(c_14769,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14046,c_28,c_372,c_511,c_518,c_546,c_791,c_1703,c_1840,c_2519,c_2674,c_5349,c_10046,c_13952,c_14047])).

cnf(c_15328,plain,
    ( k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14039,c_14769])).

cnf(c_15343,plain,
    ( r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15328,c_1532])).

cnf(c_15355,plain,
    ( r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15343,c_15328])).

cnf(c_16508,plain,
    ( v1_relat_1(X0) != iProver_top
    | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15355,c_519,c_2672])).

cnf(c_16509,plain,
    ( r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16508])).

cnf(c_14044,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13954,c_1523])).

cnf(c_14034,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13954,c_2275])).

cnf(c_14623,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14044,c_14034])).

cnf(c_14624,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_14623])).

cnf(c_16514,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16509,c_14624])).

cnf(c_14042,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13954,c_1968])).

cnf(c_14050,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13954,c_1528])).

cnf(c_776,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK2) != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_777,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
    | u1_struct_0(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_776])).

cnf(c_1520,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
    | u1_struct_0(sK2) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_14043,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13954,c_1520])).

cnf(c_14051,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14043])).

cnf(c_14045,plain,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_13954,c_1878])).

cnf(c_14052,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14051,c_14045])).

cnf(c_14701,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14042,c_14050,c_14052])).

cnf(c_14714,plain,
    ( r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_14701,c_1532])).

cnf(c_14726,plain,
    ( r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14714,c_14701])).

cnf(c_16085,plain,
    ( v1_relat_1(X0) != iProver_top
    | r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14726,c_39,c_2517])).

cnf(c_16086,plain,
    ( r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16085])).

cnf(c_16091,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16086,c_14624])).

cnf(c_16227,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15328,c_16091])).

cnf(c_107,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_109,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_19400,plain,
    ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16227,c_109,c_519,c_2672])).

cnf(c_19401,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_19400])).

cnf(c_16669,plain,
    ( k4_tmap_1(sK1,sK2) = X0
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16514,c_1539])).

cnf(c_19416,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19401,c_16669])).

cnf(c_19421,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19416,c_14701])).

cnf(c_19657,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19421,c_39,c_109,c_372,c_511,c_518,c_546,c_1703,c_1840,c_2517])).

cnf(c_19658,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_19657])).

cnf(c_19659,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19658,c_1533])).

cnf(c_19660,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19659,c_14701,c_15328])).

cnf(c_19408,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19401,c_1539])).

cnf(c_14049,plain,
    ( k1_funct_1(sK3,X0) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13954,c_1529])).

cnf(c_14203,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | k1_funct_1(sK3,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14049,c_14034])).

cnf(c_14204,plain,
    ( k1_funct_1(sK3,X0) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_14203])).

cnf(c_16515,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16509,c_14204])).

cnf(c_16640,plain,
    ( k4_tmap_1(sK1,sK2) = X0
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
    | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16515,c_1539])).

cnf(c_19417,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19401,c_16640])).

cnf(c_19420,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19417,c_14701])).

cnf(c_19435,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19420,c_39,c_109,c_372,c_511,c_518,c_546,c_1703,c_1840,c_2517])).

cnf(c_19436,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
    inference(renaming,[status(thm)],[c_19435])).

cnf(c_19663,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19660,c_39,c_109,c_372,c_511,c_518,c_519,c_546,c_1703,c_1840,c_2517,c_2672,c_19408,c_19436])).

cnf(c_19665,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) != sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) != iProver_top
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19663,c_1533])).

cnf(c_16092,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16086,c_14204])).

cnf(c_16101,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15328,c_16092])).

cnf(c_16231,plain,
    ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16101,c_109,c_519,c_2672])).

cnf(c_16232,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_16231])).

cnf(c_16237,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_16232,c_1539])).

cnf(c_16362,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16237,c_372,c_511,c_518,c_546,c_1703,c_1840])).

cnf(c_16670,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_16514,c_16362])).

cnf(c_16679,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16670,c_14701])).

cnf(c_17068,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16679,c_39,c_109,c_2517])).

cnf(c_17069,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_17068])).

cnf(c_17070,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17069,c_1533])).

cnf(c_17071,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17070,c_14701,c_15328])).

cnf(c_16641,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_16515,c_16362])).

cnf(c_16650,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16641,c_14701])).

cnf(c_17742,plain,
    ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17071,c_39,c_109,c_372,c_511,c_518,c_519,c_546,c_1703,c_1840,c_2517,c_2672,c_16237,c_16650])).

cnf(c_19666,plain,
    ( sK0(sK3,k4_tmap_1(sK1,sK2)) != sK0(sK3,k4_tmap_1(sK1,sK2))
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19665,c_14701,c_15328,c_17742])).

cnf(c_19667,plain,
    ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_19666])).

cnf(c_19793,plain,
    ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19667,c_39,c_109,c_519,c_2517,c_2672])).

cnf(c_19801,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19793,c_1539])).

cnf(c_1588,plain,
    ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
    | ~ r1_tarski(sK3,k4_tmap_1(sK1,sK2))
    | sK3 = k4_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1589,plain,
    ( sK3 = k4_tmap_1(sK1,sK2)
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top
    | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1588])).

cnf(c_19834,plain,
    ( r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19801,c_39,c_109,c_372,c_511,c_518,c_519,c_546,c_1589,c_2517,c_2672,c_19667])).

cnf(c_19838,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_16514,c_19834])).

cnf(c_19841,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19838,c_14701])).

cnf(c_19809,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19793,c_16669])).

cnf(c_19814,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19809,c_14701])).

cnf(c_20076,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19841,c_39,c_109,c_372,c_511,c_518,c_546,c_1703,c_1840,c_2517,c_19814])).

cnf(c_20078,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_20076,c_1533])).

cnf(c_19839,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_16515,c_19834])).

cnf(c_19840,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19839,c_14701])).

cnf(c_19810,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19793,c_16640])).

cnf(c_19813,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19810,c_14701])).

cnf(c_19966,plain,
    ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19840,c_39,c_109,c_372,c_511,c_518,c_546,c_1703,c_1840,c_2517,c_19813])).

cnf(c_20079,plain,
    ( sK0(k4_tmap_1(sK1,sK2),sK3) != sK0(k4_tmap_1(sK1,sK2),sK3)
    | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20078,c_14701,c_15328,c_19966])).

cnf(c_20080,plain,
    ( r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_20079])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20080,c_19667,c_2672,c_2517,c_1589,c_546,c_519,c_518,c_511,c_372,c_109,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.36/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.36/1.49  
% 7.36/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.36/1.49  
% 7.36/1.49  ------  iProver source info
% 7.36/1.49  
% 7.36/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.36/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.36/1.49  git: non_committed_changes: false
% 7.36/1.49  git: last_make_outside_of_git: false
% 7.36/1.49  
% 7.36/1.49  ------ 
% 7.36/1.49  
% 7.36/1.49  ------ Input Options
% 7.36/1.49  
% 7.36/1.49  --out_options                           all
% 7.36/1.49  --tptp_safe_out                         true
% 7.36/1.49  --problem_path                          ""
% 7.36/1.49  --include_path                          ""
% 7.36/1.49  --clausifier                            res/vclausify_rel
% 7.36/1.49  --clausifier_options                    ""
% 7.36/1.49  --stdin                                 false
% 7.36/1.49  --stats_out                             all
% 7.36/1.49  
% 7.36/1.49  ------ General Options
% 7.36/1.49  
% 7.36/1.49  --fof                                   false
% 7.36/1.49  --time_out_real                         305.
% 7.36/1.49  --time_out_virtual                      -1.
% 7.36/1.49  --symbol_type_check                     false
% 7.36/1.49  --clausify_out                          false
% 7.36/1.49  --sig_cnt_out                           false
% 7.36/1.49  --trig_cnt_out                          false
% 7.36/1.49  --trig_cnt_out_tolerance                1.
% 7.36/1.49  --trig_cnt_out_sk_spl                   false
% 7.36/1.49  --abstr_cl_out                          false
% 7.36/1.49  
% 7.36/1.49  ------ Global Options
% 7.36/1.49  
% 7.36/1.49  --schedule                              default
% 7.36/1.49  --add_important_lit                     false
% 7.36/1.49  --prop_solver_per_cl                    1000
% 7.36/1.49  --min_unsat_core                        false
% 7.36/1.49  --soft_assumptions                      false
% 7.36/1.49  --soft_lemma_size                       3
% 7.36/1.49  --prop_impl_unit_size                   0
% 7.36/1.49  --prop_impl_unit                        []
% 7.36/1.49  --share_sel_clauses                     true
% 7.36/1.49  --reset_solvers                         false
% 7.36/1.49  --bc_imp_inh                            [conj_cone]
% 7.36/1.49  --conj_cone_tolerance                   3.
% 7.36/1.49  --extra_neg_conj                        none
% 7.36/1.49  --large_theory_mode                     true
% 7.36/1.49  --prolific_symb_bound                   200
% 7.36/1.49  --lt_threshold                          2000
% 7.36/1.49  --clause_weak_htbl                      true
% 7.36/1.49  --gc_record_bc_elim                     false
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing Options
% 7.36/1.49  
% 7.36/1.49  --preprocessing_flag                    true
% 7.36/1.49  --time_out_prep_mult                    0.1
% 7.36/1.49  --splitting_mode                        input
% 7.36/1.49  --splitting_grd                         true
% 7.36/1.49  --splitting_cvd                         false
% 7.36/1.49  --splitting_cvd_svl                     false
% 7.36/1.49  --splitting_nvd                         32
% 7.36/1.49  --sub_typing                            true
% 7.36/1.49  --prep_gs_sim                           true
% 7.36/1.49  --prep_unflatten                        true
% 7.36/1.49  --prep_res_sim                          true
% 7.36/1.49  --prep_upred                            true
% 7.36/1.49  --prep_sem_filter                       exhaustive
% 7.36/1.49  --prep_sem_filter_out                   false
% 7.36/1.49  --pred_elim                             true
% 7.36/1.49  --res_sim_input                         true
% 7.36/1.49  --eq_ax_congr_red                       true
% 7.36/1.49  --pure_diseq_elim                       true
% 7.36/1.49  --brand_transform                       false
% 7.36/1.49  --non_eq_to_eq                          false
% 7.36/1.49  --prep_def_merge                        true
% 7.36/1.49  --prep_def_merge_prop_impl              false
% 7.36/1.49  --prep_def_merge_mbd                    true
% 7.36/1.49  --prep_def_merge_tr_red                 false
% 7.36/1.49  --prep_def_merge_tr_cl                  false
% 7.36/1.49  --smt_preprocessing                     true
% 7.36/1.49  --smt_ac_axioms                         fast
% 7.36/1.49  --preprocessed_out                      false
% 7.36/1.49  --preprocessed_stats                    false
% 7.36/1.49  
% 7.36/1.49  ------ Abstraction refinement Options
% 7.36/1.49  
% 7.36/1.49  --abstr_ref                             []
% 7.36/1.49  --abstr_ref_prep                        false
% 7.36/1.49  --abstr_ref_until_sat                   false
% 7.36/1.49  --abstr_ref_sig_restrict                funpre
% 7.36/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.36/1.49  --abstr_ref_under                       []
% 7.36/1.49  
% 7.36/1.49  ------ SAT Options
% 7.36/1.49  
% 7.36/1.49  --sat_mode                              false
% 7.36/1.49  --sat_fm_restart_options                ""
% 7.36/1.49  --sat_gr_def                            false
% 7.36/1.49  --sat_epr_types                         true
% 7.36/1.49  --sat_non_cyclic_types                  false
% 7.36/1.49  --sat_finite_models                     false
% 7.36/1.49  --sat_fm_lemmas                         false
% 7.36/1.49  --sat_fm_prep                           false
% 7.36/1.49  --sat_fm_uc_incr                        true
% 7.36/1.49  --sat_out_model                         small
% 7.36/1.49  --sat_out_clauses                       false
% 7.36/1.49  
% 7.36/1.49  ------ QBF Options
% 7.36/1.49  
% 7.36/1.49  --qbf_mode                              false
% 7.36/1.49  --qbf_elim_univ                         false
% 7.36/1.49  --qbf_dom_inst                          none
% 7.36/1.49  --qbf_dom_pre_inst                      false
% 7.36/1.49  --qbf_sk_in                             false
% 7.36/1.49  --qbf_pred_elim                         true
% 7.36/1.49  --qbf_split                             512
% 7.36/1.49  
% 7.36/1.49  ------ BMC1 Options
% 7.36/1.49  
% 7.36/1.49  --bmc1_incremental                      false
% 7.36/1.49  --bmc1_axioms                           reachable_all
% 7.36/1.49  --bmc1_min_bound                        0
% 7.36/1.49  --bmc1_max_bound                        -1
% 7.36/1.49  --bmc1_max_bound_default                -1
% 7.36/1.49  --bmc1_symbol_reachability              true
% 7.36/1.49  --bmc1_property_lemmas                  false
% 7.36/1.49  --bmc1_k_induction                      false
% 7.36/1.49  --bmc1_non_equiv_states                 false
% 7.36/1.49  --bmc1_deadlock                         false
% 7.36/1.49  --bmc1_ucm                              false
% 7.36/1.49  --bmc1_add_unsat_core                   none
% 7.36/1.49  --bmc1_unsat_core_children              false
% 7.36/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.36/1.49  --bmc1_out_stat                         full
% 7.36/1.49  --bmc1_ground_init                      false
% 7.36/1.49  --bmc1_pre_inst_next_state              false
% 7.36/1.49  --bmc1_pre_inst_state                   false
% 7.36/1.49  --bmc1_pre_inst_reach_state             false
% 7.36/1.49  --bmc1_out_unsat_core                   false
% 7.36/1.49  --bmc1_aig_witness_out                  false
% 7.36/1.49  --bmc1_verbose                          false
% 7.36/1.49  --bmc1_dump_clauses_tptp                false
% 7.36/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.36/1.49  --bmc1_dump_file                        -
% 7.36/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.36/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.36/1.49  --bmc1_ucm_extend_mode                  1
% 7.36/1.49  --bmc1_ucm_init_mode                    2
% 7.36/1.49  --bmc1_ucm_cone_mode                    none
% 7.36/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.36/1.49  --bmc1_ucm_relax_model                  4
% 7.36/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.36/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.36/1.49  --bmc1_ucm_layered_model                none
% 7.36/1.49  --bmc1_ucm_max_lemma_size               10
% 7.36/1.49  
% 7.36/1.49  ------ AIG Options
% 7.36/1.49  
% 7.36/1.49  --aig_mode                              false
% 7.36/1.49  
% 7.36/1.49  ------ Instantiation Options
% 7.36/1.49  
% 7.36/1.49  --instantiation_flag                    true
% 7.36/1.49  --inst_sos_flag                         true
% 7.36/1.49  --inst_sos_phase                        true
% 7.36/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.36/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.36/1.49  --inst_lit_sel_side                     num_symb
% 7.36/1.49  --inst_solver_per_active                1400
% 7.36/1.49  --inst_solver_calls_frac                1.
% 7.36/1.49  --inst_passive_queue_type               priority_queues
% 7.36/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.36/1.49  --inst_passive_queues_freq              [25;2]
% 7.36/1.49  --inst_dismatching                      true
% 7.36/1.49  --inst_eager_unprocessed_to_passive     true
% 7.36/1.49  --inst_prop_sim_given                   true
% 7.36/1.49  --inst_prop_sim_new                     false
% 7.36/1.49  --inst_subs_new                         false
% 7.36/1.49  --inst_eq_res_simp                      false
% 7.36/1.49  --inst_subs_given                       false
% 7.36/1.49  --inst_orphan_elimination               true
% 7.36/1.49  --inst_learning_loop_flag               true
% 7.36/1.49  --inst_learning_start                   3000
% 7.36/1.49  --inst_learning_factor                  2
% 7.36/1.49  --inst_start_prop_sim_after_learn       3
% 7.36/1.49  --inst_sel_renew                        solver
% 7.36/1.49  --inst_lit_activity_flag                true
% 7.36/1.49  --inst_restr_to_given                   false
% 7.36/1.49  --inst_activity_threshold               500
% 7.36/1.49  --inst_out_proof                        true
% 7.36/1.49  
% 7.36/1.49  ------ Resolution Options
% 7.36/1.49  
% 7.36/1.49  --resolution_flag                       true
% 7.36/1.49  --res_lit_sel                           adaptive
% 7.36/1.49  --res_lit_sel_side                      none
% 7.36/1.49  --res_ordering                          kbo
% 7.36/1.49  --res_to_prop_solver                    active
% 7.36/1.49  --res_prop_simpl_new                    false
% 7.36/1.49  --res_prop_simpl_given                  true
% 7.36/1.49  --res_passive_queue_type                priority_queues
% 7.36/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.36/1.49  --res_passive_queues_freq               [15;5]
% 7.36/1.49  --res_forward_subs                      full
% 7.36/1.49  --res_backward_subs                     full
% 7.36/1.49  --res_forward_subs_resolution           true
% 7.36/1.49  --res_backward_subs_resolution          true
% 7.36/1.49  --res_orphan_elimination                true
% 7.36/1.49  --res_time_limit                        2.
% 7.36/1.49  --res_out_proof                         true
% 7.36/1.49  
% 7.36/1.49  ------ Superposition Options
% 7.36/1.49  
% 7.36/1.49  --superposition_flag                    true
% 7.36/1.49  --sup_passive_queue_type                priority_queues
% 7.36/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.36/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.36/1.49  --demod_completeness_check              fast
% 7.36/1.49  --demod_use_ground                      true
% 7.36/1.49  --sup_to_prop_solver                    passive
% 7.36/1.49  --sup_prop_simpl_new                    true
% 7.36/1.49  --sup_prop_simpl_given                  true
% 7.36/1.49  --sup_fun_splitting                     true
% 7.36/1.49  --sup_smt_interval                      50000
% 7.36/1.49  
% 7.36/1.49  ------ Superposition Simplification Setup
% 7.36/1.49  
% 7.36/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.36/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.36/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.36/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.36/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.36/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.36/1.49  --sup_immed_triv                        [TrivRules]
% 7.36/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_immed_bw_main                     []
% 7.36/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.36/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.36/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_input_bw                          []
% 7.36/1.49  
% 7.36/1.49  ------ Combination Options
% 7.36/1.49  
% 7.36/1.49  --comb_res_mult                         3
% 7.36/1.49  --comb_sup_mult                         2
% 7.36/1.49  --comb_inst_mult                        10
% 7.36/1.49  
% 7.36/1.49  ------ Debug Options
% 7.36/1.49  
% 7.36/1.49  --dbg_backtrace                         false
% 7.36/1.49  --dbg_dump_prop_clauses                 false
% 7.36/1.49  --dbg_dump_prop_clauses_file            -
% 7.36/1.49  --dbg_out_stat                          false
% 7.36/1.49  ------ Parsing...
% 7.36/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.36/1.49  ------ Proving...
% 7.36/1.49  ------ Problem Properties 
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  clauses                                 24
% 7.36/1.49  conjectures                             3
% 7.36/1.49  EPR                                     3
% 7.36/1.49  Horn                                    19
% 7.36/1.49  unary                                   8
% 7.36/1.49  binary                                  3
% 7.36/1.49  lits                                    70
% 7.36/1.49  lits eq                                 21
% 7.36/1.49  fd_pure                                 0
% 7.36/1.49  fd_pseudo                               0
% 7.36/1.49  fd_cond                                 0
% 7.36/1.49  fd_pseudo_cond                          1
% 7.36/1.49  AC symbols                              0
% 7.36/1.49  
% 7.36/1.49  ------ Schedule dynamic 5 is on 
% 7.36/1.49  
% 7.36/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  ------ 
% 7.36/1.49  Current options:
% 7.36/1.49  ------ 
% 7.36/1.49  
% 7.36/1.49  ------ Input Options
% 7.36/1.49  
% 7.36/1.49  --out_options                           all
% 7.36/1.49  --tptp_safe_out                         true
% 7.36/1.49  --problem_path                          ""
% 7.36/1.49  --include_path                          ""
% 7.36/1.49  --clausifier                            res/vclausify_rel
% 7.36/1.49  --clausifier_options                    ""
% 7.36/1.49  --stdin                                 false
% 7.36/1.49  --stats_out                             all
% 7.36/1.49  
% 7.36/1.49  ------ General Options
% 7.36/1.49  
% 7.36/1.49  --fof                                   false
% 7.36/1.49  --time_out_real                         305.
% 7.36/1.49  --time_out_virtual                      -1.
% 7.36/1.49  --symbol_type_check                     false
% 7.36/1.49  --clausify_out                          false
% 7.36/1.49  --sig_cnt_out                           false
% 7.36/1.49  --trig_cnt_out                          false
% 7.36/1.49  --trig_cnt_out_tolerance                1.
% 7.36/1.49  --trig_cnt_out_sk_spl                   false
% 7.36/1.49  --abstr_cl_out                          false
% 7.36/1.49  
% 7.36/1.49  ------ Global Options
% 7.36/1.49  
% 7.36/1.49  --schedule                              default
% 7.36/1.49  --add_important_lit                     false
% 7.36/1.49  --prop_solver_per_cl                    1000
% 7.36/1.49  --min_unsat_core                        false
% 7.36/1.49  --soft_assumptions                      false
% 7.36/1.49  --soft_lemma_size                       3
% 7.36/1.49  --prop_impl_unit_size                   0
% 7.36/1.49  --prop_impl_unit                        []
% 7.36/1.49  --share_sel_clauses                     true
% 7.36/1.49  --reset_solvers                         false
% 7.36/1.49  --bc_imp_inh                            [conj_cone]
% 7.36/1.49  --conj_cone_tolerance                   3.
% 7.36/1.49  --extra_neg_conj                        none
% 7.36/1.49  --large_theory_mode                     true
% 7.36/1.49  --prolific_symb_bound                   200
% 7.36/1.49  --lt_threshold                          2000
% 7.36/1.49  --clause_weak_htbl                      true
% 7.36/1.49  --gc_record_bc_elim                     false
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing Options
% 7.36/1.49  
% 7.36/1.49  --preprocessing_flag                    true
% 7.36/1.49  --time_out_prep_mult                    0.1
% 7.36/1.49  --splitting_mode                        input
% 7.36/1.49  --splitting_grd                         true
% 7.36/1.49  --splitting_cvd                         false
% 7.36/1.49  --splitting_cvd_svl                     false
% 7.36/1.49  --splitting_nvd                         32
% 7.36/1.49  --sub_typing                            true
% 7.36/1.49  --prep_gs_sim                           true
% 7.36/1.49  --prep_unflatten                        true
% 7.36/1.49  --prep_res_sim                          true
% 7.36/1.49  --prep_upred                            true
% 7.36/1.49  --prep_sem_filter                       exhaustive
% 7.36/1.49  --prep_sem_filter_out                   false
% 7.36/1.49  --pred_elim                             true
% 7.36/1.49  --res_sim_input                         true
% 7.36/1.49  --eq_ax_congr_red                       true
% 7.36/1.49  --pure_diseq_elim                       true
% 7.36/1.49  --brand_transform                       false
% 7.36/1.49  --non_eq_to_eq                          false
% 7.36/1.49  --prep_def_merge                        true
% 7.36/1.49  --prep_def_merge_prop_impl              false
% 7.36/1.49  --prep_def_merge_mbd                    true
% 7.36/1.49  --prep_def_merge_tr_red                 false
% 7.36/1.49  --prep_def_merge_tr_cl                  false
% 7.36/1.49  --smt_preprocessing                     true
% 7.36/1.49  --smt_ac_axioms                         fast
% 7.36/1.49  --preprocessed_out                      false
% 7.36/1.49  --preprocessed_stats                    false
% 7.36/1.49  
% 7.36/1.49  ------ Abstraction refinement Options
% 7.36/1.49  
% 7.36/1.49  --abstr_ref                             []
% 7.36/1.49  --abstr_ref_prep                        false
% 7.36/1.49  --abstr_ref_until_sat                   false
% 7.36/1.49  --abstr_ref_sig_restrict                funpre
% 7.36/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.36/1.49  --abstr_ref_under                       []
% 7.36/1.49  
% 7.36/1.49  ------ SAT Options
% 7.36/1.49  
% 7.36/1.49  --sat_mode                              false
% 7.36/1.49  --sat_fm_restart_options                ""
% 7.36/1.49  --sat_gr_def                            false
% 7.36/1.49  --sat_epr_types                         true
% 7.36/1.49  --sat_non_cyclic_types                  false
% 7.36/1.49  --sat_finite_models                     false
% 7.36/1.49  --sat_fm_lemmas                         false
% 7.36/1.49  --sat_fm_prep                           false
% 7.36/1.49  --sat_fm_uc_incr                        true
% 7.36/1.49  --sat_out_model                         small
% 7.36/1.49  --sat_out_clauses                       false
% 7.36/1.49  
% 7.36/1.49  ------ QBF Options
% 7.36/1.49  
% 7.36/1.49  --qbf_mode                              false
% 7.36/1.49  --qbf_elim_univ                         false
% 7.36/1.49  --qbf_dom_inst                          none
% 7.36/1.49  --qbf_dom_pre_inst                      false
% 7.36/1.49  --qbf_sk_in                             false
% 7.36/1.49  --qbf_pred_elim                         true
% 7.36/1.49  --qbf_split                             512
% 7.36/1.49  
% 7.36/1.49  ------ BMC1 Options
% 7.36/1.49  
% 7.36/1.49  --bmc1_incremental                      false
% 7.36/1.49  --bmc1_axioms                           reachable_all
% 7.36/1.49  --bmc1_min_bound                        0
% 7.36/1.49  --bmc1_max_bound                        -1
% 7.36/1.49  --bmc1_max_bound_default                -1
% 7.36/1.49  --bmc1_symbol_reachability              true
% 7.36/1.49  --bmc1_property_lemmas                  false
% 7.36/1.49  --bmc1_k_induction                      false
% 7.36/1.49  --bmc1_non_equiv_states                 false
% 7.36/1.49  --bmc1_deadlock                         false
% 7.36/1.49  --bmc1_ucm                              false
% 7.36/1.49  --bmc1_add_unsat_core                   none
% 7.36/1.49  --bmc1_unsat_core_children              false
% 7.36/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.36/1.49  --bmc1_out_stat                         full
% 7.36/1.49  --bmc1_ground_init                      false
% 7.36/1.49  --bmc1_pre_inst_next_state              false
% 7.36/1.49  --bmc1_pre_inst_state                   false
% 7.36/1.49  --bmc1_pre_inst_reach_state             false
% 7.36/1.49  --bmc1_out_unsat_core                   false
% 7.36/1.49  --bmc1_aig_witness_out                  false
% 7.36/1.49  --bmc1_verbose                          false
% 7.36/1.49  --bmc1_dump_clauses_tptp                false
% 7.36/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.36/1.49  --bmc1_dump_file                        -
% 7.36/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.36/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.36/1.49  --bmc1_ucm_extend_mode                  1
% 7.36/1.49  --bmc1_ucm_init_mode                    2
% 7.36/1.49  --bmc1_ucm_cone_mode                    none
% 7.36/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.36/1.49  --bmc1_ucm_relax_model                  4
% 7.36/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.36/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.36/1.49  --bmc1_ucm_layered_model                none
% 7.36/1.49  --bmc1_ucm_max_lemma_size               10
% 7.36/1.49  
% 7.36/1.49  ------ AIG Options
% 7.36/1.49  
% 7.36/1.49  --aig_mode                              false
% 7.36/1.49  
% 7.36/1.49  ------ Instantiation Options
% 7.36/1.49  
% 7.36/1.49  --instantiation_flag                    true
% 7.36/1.49  --inst_sos_flag                         true
% 7.36/1.49  --inst_sos_phase                        true
% 7.36/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.36/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.36/1.49  --inst_lit_sel_side                     none
% 7.36/1.49  --inst_solver_per_active                1400
% 7.36/1.49  --inst_solver_calls_frac                1.
% 7.36/1.49  --inst_passive_queue_type               priority_queues
% 7.36/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.36/1.49  --inst_passive_queues_freq              [25;2]
% 7.36/1.49  --inst_dismatching                      true
% 7.36/1.49  --inst_eager_unprocessed_to_passive     true
% 7.36/1.49  --inst_prop_sim_given                   true
% 7.36/1.49  --inst_prop_sim_new                     false
% 7.36/1.49  --inst_subs_new                         false
% 7.36/1.49  --inst_eq_res_simp                      false
% 7.36/1.49  --inst_subs_given                       false
% 7.36/1.49  --inst_orphan_elimination               true
% 7.36/1.49  --inst_learning_loop_flag               true
% 7.36/1.49  --inst_learning_start                   3000
% 7.36/1.49  --inst_learning_factor                  2
% 7.36/1.49  --inst_start_prop_sim_after_learn       3
% 7.36/1.49  --inst_sel_renew                        solver
% 7.36/1.49  --inst_lit_activity_flag                true
% 7.36/1.49  --inst_restr_to_given                   false
% 7.36/1.49  --inst_activity_threshold               500
% 7.36/1.49  --inst_out_proof                        true
% 7.36/1.49  
% 7.36/1.49  ------ Resolution Options
% 7.36/1.49  
% 7.36/1.49  --resolution_flag                       false
% 7.36/1.49  --res_lit_sel                           adaptive
% 7.36/1.49  --res_lit_sel_side                      none
% 7.36/1.49  --res_ordering                          kbo
% 7.36/1.49  --res_to_prop_solver                    active
% 7.36/1.49  --res_prop_simpl_new                    false
% 7.36/1.49  --res_prop_simpl_given                  true
% 7.36/1.49  --res_passive_queue_type                priority_queues
% 7.36/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.36/1.49  --res_passive_queues_freq               [15;5]
% 7.36/1.49  --res_forward_subs                      full
% 7.36/1.49  --res_backward_subs                     full
% 7.36/1.49  --res_forward_subs_resolution           true
% 7.36/1.49  --res_backward_subs_resolution          true
% 7.36/1.49  --res_orphan_elimination                true
% 7.36/1.49  --res_time_limit                        2.
% 7.36/1.49  --res_out_proof                         true
% 7.36/1.49  
% 7.36/1.49  ------ Superposition Options
% 7.36/1.49  
% 7.36/1.49  --superposition_flag                    true
% 7.36/1.49  --sup_passive_queue_type                priority_queues
% 7.36/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.36/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.36/1.49  --demod_completeness_check              fast
% 7.36/1.49  --demod_use_ground                      true
% 7.36/1.49  --sup_to_prop_solver                    passive
% 7.36/1.49  --sup_prop_simpl_new                    true
% 7.36/1.49  --sup_prop_simpl_given                  true
% 7.36/1.49  --sup_fun_splitting                     true
% 7.36/1.49  --sup_smt_interval                      50000
% 7.36/1.49  
% 7.36/1.49  ------ Superposition Simplification Setup
% 7.36/1.49  
% 7.36/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.36/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.36/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.36/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.36/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.36/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.36/1.49  --sup_immed_triv                        [TrivRules]
% 7.36/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_immed_bw_main                     []
% 7.36/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.36/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.36/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_input_bw                          []
% 7.36/1.49  
% 7.36/1.49  ------ Combination Options
% 7.36/1.49  
% 7.36/1.49  --comb_res_mult                         3
% 7.36/1.49  --comb_sup_mult                         2
% 7.36/1.49  --comb_inst_mult                        10
% 7.36/1.49  
% 7.36/1.49  ------ Debug Options
% 7.36/1.49  
% 7.36/1.49  --dbg_backtrace                         false
% 7.36/1.49  --dbg_dump_prop_clauses                 false
% 7.36/1.49  --dbg_dump_prop_clauses_file            -
% 7.36/1.49  --dbg_out_stat                          false
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  ------ Proving...
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  % SZS status Theorem for theBenchmark.p
% 7.36/1.49  
% 7.36/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.36/1.49  
% 7.36/1.49  fof(f8,axiom,(
% 7.36/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,X1) <=> (! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f22,plain,(
% 7.36/1.49    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.36/1.49    inference(ennf_transformation,[],[f8])).
% 7.36/1.49  
% 7.36/1.49  fof(f23,plain,(
% 7.36/1.49    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(flattening,[],[f22])).
% 7.36/1.49  
% 7.36/1.49  fof(f35,plain,(
% 7.36/1.49    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) & ((! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(nnf_transformation,[],[f23])).
% 7.36/1.49  
% 7.36/1.49  fof(f36,plain,(
% 7.36/1.49    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(flattening,[],[f35])).
% 7.36/1.49  
% 7.36/1.49  fof(f37,plain,(
% 7.36/1.49    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(rectify,[],[f36])).
% 7.36/1.49  
% 7.36/1.49  fof(f38,plain,(
% 7.36/1.49    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 7.36/1.49    introduced(choice_axiom,[])).
% 7.36/1.49  
% 7.36/1.49  fof(f39,plain,(
% 7.36/1.49    ! [X0] : (! [X1] : (((r1_tarski(X0,X1) | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & ((! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 7.36/1.49  
% 7.36/1.49  fof(f59,plain,(
% 7.36/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f39])).
% 7.36/1.49  
% 7.36/1.49  fof(f12,conjecture,(
% 7.36/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f13,negated_conjecture,(
% 7.36/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 7.36/1.49    inference(negated_conjecture,[],[f12])).
% 7.36/1.49  
% 7.36/1.49  fof(f29,plain,(
% 7.36/1.49    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.36/1.49    inference(ennf_transformation,[],[f13])).
% 7.36/1.49  
% 7.36/1.49  fof(f30,plain,(
% 7.36/1.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.36/1.49    inference(flattening,[],[f29])).
% 7.36/1.49  
% 7.36/1.49  fof(f42,plain,(
% 7.36/1.49    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 7.36/1.49    introduced(choice_axiom,[])).
% 7.36/1.49  
% 7.36/1.49  fof(f41,plain,(
% 7.36/1.49    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.36/1.49    introduced(choice_axiom,[])).
% 7.36/1.49  
% 7.36/1.49  fof(f40,plain,(
% 7.36/1.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 7.36/1.49    introduced(choice_axiom,[])).
% 7.36/1.49  
% 7.36/1.49  fof(f43,plain,(
% 7.36/1.49    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 7.36/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f42,f41,f40])).
% 7.36/1.49  
% 7.36/1.49  fof(f75,plain,(
% 7.36/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 7.36/1.49    inference(cnf_transformation,[],[f43])).
% 7.36/1.49  
% 7.36/1.49  fof(f5,axiom,(
% 7.36/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f17,plain,(
% 7.36/1.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.36/1.49    inference(ennf_transformation,[],[f5])).
% 7.36/1.49  
% 7.36/1.49  fof(f50,plain,(
% 7.36/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.36/1.49    inference(cnf_transformation,[],[f17])).
% 7.36/1.49  
% 7.36/1.49  fof(f6,axiom,(
% 7.36/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f18,plain,(
% 7.36/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.36/1.49    inference(ennf_transformation,[],[f6])).
% 7.36/1.49  
% 7.36/1.49  fof(f19,plain,(
% 7.36/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.36/1.49    inference(flattening,[],[f18])).
% 7.36/1.49  
% 7.36/1.49  fof(f33,plain,(
% 7.36/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.36/1.49    inference(nnf_transformation,[],[f19])).
% 7.36/1.49  
% 7.36/1.49  fof(f51,plain,(
% 7.36/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.36/1.49    inference(cnf_transformation,[],[f33])).
% 7.36/1.49  
% 7.36/1.49  fof(f74,plain,(
% 7.36/1.49    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 7.36/1.49    inference(cnf_transformation,[],[f43])).
% 7.36/1.49  
% 7.36/1.49  fof(f55,plain,(
% 7.36/1.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.36/1.49    inference(cnf_transformation,[],[f33])).
% 7.36/1.49  
% 7.36/1.49  fof(f82,plain,(
% 7.36/1.49    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.36/1.49    inference(equality_resolution,[],[f55])).
% 7.36/1.49  
% 7.36/1.49  fof(f7,axiom,(
% 7.36/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f20,plain,(
% 7.36/1.49    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.36/1.49    inference(ennf_transformation,[],[f7])).
% 7.36/1.49  
% 7.36/1.49  fof(f21,plain,(
% 7.36/1.49    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.36/1.49    inference(flattening,[],[f20])).
% 7.36/1.49  
% 7.36/1.49  fof(f34,plain,(
% 7.36/1.49    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.36/1.49    inference(nnf_transformation,[],[f21])).
% 7.36/1.49  
% 7.36/1.49  fof(f58,plain,(
% 7.36/1.49    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f34])).
% 7.36/1.49  
% 7.36/1.49  fof(f85,plain,(
% 7.36/1.49    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.36/1.49    inference(equality_resolution,[],[f58])).
% 7.36/1.49  
% 7.36/1.49  fof(f77,plain,(
% 7.36/1.49    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)),
% 7.36/1.49    inference(cnf_transformation,[],[f43])).
% 7.36/1.49  
% 7.36/1.49  fof(f72,plain,(
% 7.36/1.49    m1_pre_topc(sK2,sK1)),
% 7.36/1.49    inference(cnf_transformation,[],[f43])).
% 7.36/1.49  
% 7.36/1.49  fof(f9,axiom,(
% 7.36/1.49    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f24,plain,(
% 7.36/1.49    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.36/1.49    inference(ennf_transformation,[],[f9])).
% 7.36/1.49  
% 7.36/1.49  fof(f25,plain,(
% 7.36/1.49    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.36/1.49    inference(flattening,[],[f24])).
% 7.36/1.49  
% 7.36/1.49  fof(f65,plain,(
% 7.36/1.49    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f25])).
% 7.36/1.49  
% 7.36/1.49  fof(f69,plain,(
% 7.36/1.49    v2_pre_topc(sK1)),
% 7.36/1.49    inference(cnf_transformation,[],[f43])).
% 7.36/1.49  
% 7.36/1.49  fof(f68,plain,(
% 7.36/1.49    ~v2_struct_0(sK1)),
% 7.36/1.49    inference(cnf_transformation,[],[f43])).
% 7.36/1.49  
% 7.36/1.49  fof(f70,plain,(
% 7.36/1.49    l1_pre_topc(sK1)),
% 7.36/1.49    inference(cnf_transformation,[],[f43])).
% 7.36/1.49  
% 7.36/1.49  fof(f63,plain,(
% 7.36/1.49    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f25])).
% 7.36/1.49  
% 7.36/1.49  fof(f64,plain,(
% 7.36/1.49    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f25])).
% 7.36/1.49  
% 7.36/1.49  fof(f61,plain,(
% 7.36/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f39])).
% 7.36/1.49  
% 7.36/1.49  fof(f11,axiom,(
% 7.36/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f27,plain,(
% 7.36/1.49    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.36/1.49    inference(ennf_transformation,[],[f11])).
% 7.36/1.49  
% 7.36/1.49  fof(f28,plain,(
% 7.36/1.49    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.36/1.49    inference(flattening,[],[f27])).
% 7.36/1.49  
% 7.36/1.49  fof(f67,plain,(
% 7.36/1.49    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f28])).
% 7.36/1.49  
% 7.36/1.49  fof(f71,plain,(
% 7.36/1.49    ~v2_struct_0(sK2)),
% 7.36/1.49    inference(cnf_transformation,[],[f43])).
% 7.36/1.49  
% 7.36/1.49  fof(f10,axiom,(
% 7.36/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f26,plain,(
% 7.36/1.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.36/1.49    inference(ennf_transformation,[],[f10])).
% 7.36/1.49  
% 7.36/1.49  fof(f66,plain,(
% 7.36/1.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f26])).
% 7.36/1.49  
% 7.36/1.49  fof(f2,axiom,(
% 7.36/1.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f14,plain,(
% 7.36/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.36/1.49    inference(ennf_transformation,[],[f2])).
% 7.36/1.49  
% 7.36/1.49  fof(f15,plain,(
% 7.36/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.36/1.49    inference(flattening,[],[f14])).
% 7.36/1.49  
% 7.36/1.49  fof(f47,plain,(
% 7.36/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f15])).
% 7.36/1.49  
% 7.36/1.49  fof(f73,plain,(
% 7.36/1.49    v1_funct_1(sK3)),
% 7.36/1.49    inference(cnf_transformation,[],[f43])).
% 7.36/1.49  
% 7.36/1.49  fof(f4,axiom,(
% 7.36/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f49,plain,(
% 7.36/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.36/1.49    inference(cnf_transformation,[],[f4])).
% 7.36/1.49  
% 7.36/1.49  fof(f3,axiom,(
% 7.36/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f16,plain,(
% 7.36/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(ennf_transformation,[],[f3])).
% 7.36/1.49  
% 7.36/1.49  fof(f48,plain,(
% 7.36/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f16])).
% 7.36/1.49  
% 7.36/1.49  fof(f1,axiom,(
% 7.36/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f31,plain,(
% 7.36/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.36/1.49    inference(nnf_transformation,[],[f1])).
% 7.36/1.49  
% 7.36/1.49  fof(f32,plain,(
% 7.36/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.36/1.49    inference(flattening,[],[f31])).
% 7.36/1.49  
% 7.36/1.49  fof(f45,plain,(
% 7.36/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.36/1.49    inference(cnf_transformation,[],[f32])).
% 7.36/1.49  
% 7.36/1.49  fof(f78,plain,(
% 7.36/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.36/1.49    inference(equality_resolution,[],[f45])).
% 7.36/1.49  
% 7.36/1.49  fof(f44,plain,(
% 7.36/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.36/1.49    inference(cnf_transformation,[],[f32])).
% 7.36/1.49  
% 7.36/1.49  fof(f79,plain,(
% 7.36/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.36/1.49    inference(equality_resolution,[],[f44])).
% 7.36/1.49  
% 7.36/1.49  fof(f46,plain,(
% 7.36/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f32])).
% 7.36/1.49  
% 7.36/1.49  fof(f62,plain,(
% 7.36/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f39])).
% 7.36/1.49  
% 7.36/1.49  fof(f76,plain,(
% 7.36/1.49    ( ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) )),
% 7.36/1.49    inference(cnf_transformation,[],[f43])).
% 7.36/1.49  
% 7.36/1.49  fof(f60,plain,(
% 7.36/1.49    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_tarski(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f39])).
% 7.36/1.49  
% 7.36/1.49  fof(f52,plain,(
% 7.36/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.36/1.49    inference(cnf_transformation,[],[f33])).
% 7.36/1.49  
% 7.36/1.49  fof(f84,plain,(
% 7.36/1.49    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.36/1.49    inference(equality_resolution,[],[f52])).
% 7.36/1.49  
% 7.36/1.49  cnf(c_18,plain,
% 7.36/1.49      ( ~ r1_tarski(X0,X1)
% 7.36/1.49      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.36/1.49      | ~ v1_funct_1(X1)
% 7.36/1.49      | ~ v1_funct_1(X0)
% 7.36/1.49      | ~ v1_relat_1(X0)
% 7.36/1.49      | ~ v1_relat_1(X1) ),
% 7.36/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1530,plain,
% 7.36/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.36/1.49      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 7.36/1.49      | v1_funct_1(X1) != iProver_top
% 7.36/1.49      | v1_funct_1(X0) != iProver_top
% 7.36/1.49      | v1_relat_1(X0) != iProver_top
% 7.36/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_26,negated_conjecture,
% 7.36/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 7.36/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1528,plain,
% 7.36/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_6,plain,
% 7.36/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.36/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.36/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1534,plain,
% 7.36/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.36/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1878,plain,
% 7.36/1.49      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_1528,c_1534]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_12,plain,
% 7.36/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.36/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.36/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.36/1.49      | k1_xboole_0 = X2 ),
% 7.36/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_27,negated_conjecture,
% 7.36/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 7.36/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_802,plain,
% 7.36/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.36/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.36/1.49      | u1_struct_0(sK1) != X2
% 7.36/1.49      | u1_struct_0(sK2) != X1
% 7.36/1.49      | sK3 != X0
% 7.36/1.49      | k1_xboole_0 = X2 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_803,plain,
% 7.36/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.36/1.49      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3) = u1_struct_0(sK2)
% 7.36/1.49      | k1_xboole_0 = u1_struct_0(sK1) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_802]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_805,plain,
% 7.36/1.49      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3) = u1_struct_0(sK2)
% 7.36/1.49      | k1_xboole_0 = u1_struct_0(sK1) ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_803,c_26]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1968,plain,
% 7.36/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.49      | u1_struct_0(sK2) = k1_relat_1(sK3) ),
% 7.36/1.49      inference(demodulation,[status(thm)],[c_1878,c_805]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_8,plain,
% 7.36/1.49      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.36/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.36/1.49      | k1_xboole_0 = X1
% 7.36/1.49      | k1_xboole_0 = X0 ),
% 7.36/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_740,plain,
% 7.36/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.36/1.49      | u1_struct_0(sK1) != k1_xboole_0
% 7.36/1.49      | u1_struct_0(sK2) != X1
% 7.36/1.49      | sK3 != X0
% 7.36/1.49      | k1_xboole_0 = X0
% 7.36/1.49      | k1_xboole_0 = X1 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_741,plain,
% 7.36/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.36/1.49      | u1_struct_0(sK1) != k1_xboole_0
% 7.36/1.49      | k1_xboole_0 = u1_struct_0(sK2)
% 7.36/1.49      | k1_xboole_0 = sK3 ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_740]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1522,plain,
% 7.36/1.49      ( u1_struct_0(sK1) != k1_xboole_0
% 7.36/1.49      | k1_xboole_0 = u1_struct_0(sK2)
% 7.36/1.49      | k1_xboole_0 = sK3
% 7.36/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2177,plain,
% 7.36/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK3)
% 7.36/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.49      | sK3 = k1_xboole_0
% 7.36/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_1968,c_1522]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_13,plain,
% 7.36/1.49      ( r2_funct_2(X0,X1,X2,X2)
% 7.36/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.36/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.36/1.49      | ~ v1_funct_1(X2) ),
% 7.36/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_24,negated_conjecture,
% 7.36/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
% 7.36/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_371,plain,
% 7.36/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.36/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.36/1.49      | ~ v1_funct_1(X0)
% 7.36/1.49      | k4_tmap_1(sK1,sK2) != X0
% 7.36/1.49      | u1_struct_0(sK1) != X2
% 7.36/1.49      | u1_struct_0(sK2) != X1
% 7.36/1.49      | sK3 != X0 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_372,plain,
% 7.36/1.49      ( ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.36/1.49      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.36/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.36/1.49      | sK3 != k4_tmap_1(sK1,sK2) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_371]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_29,negated_conjecture,
% 7.36/1.49      ( m1_pre_topc(sK2,sK1) ),
% 7.36/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_19,plain,
% 7.36/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.36/1.49      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.36/1.49      | v2_struct_0(X1)
% 7.36/1.49      | ~ v2_pre_topc(X1)
% 7.36/1.49      | ~ l1_pre_topc(X1) ),
% 7.36/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_32,negated_conjecture,
% 7.36/1.49      ( v2_pre_topc(sK1) ),
% 7.36/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_455,plain,
% 7.36/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.36/1.49      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.36/1.49      | v2_struct_0(X1)
% 7.36/1.49      | ~ l1_pre_topc(X1)
% 7.36/1.49      | sK1 != X1 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_32]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_456,plain,
% 7.36/1.49      ( ~ m1_pre_topc(X0,sK1)
% 7.36/1.49      | m1_subset_1(k4_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 7.36/1.49      | v2_struct_0(sK1)
% 7.36/1.49      | ~ l1_pre_topc(sK1) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_455]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_33,negated_conjecture,
% 7.36/1.49      ( ~ v2_struct_0(sK1) ),
% 7.36/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_31,negated_conjecture,
% 7.36/1.49      ( l1_pre_topc(sK1) ),
% 7.36/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_460,plain,
% 7.36/1.49      ( ~ m1_pre_topc(X0,sK1)
% 7.36/1.49      | m1_subset_1(k4_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_456,c_33,c_31]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_510,plain,
% 7.36/1.49      ( m1_subset_1(k4_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 7.36/1.49      | sK1 != sK1
% 7.36/1.49      | sK2 != X0 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_29,c_460]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_511,plain,
% 7.36/1.49      ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_510]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_21,plain,
% 7.36/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.36/1.49      | v2_struct_0(X1)
% 7.36/1.49      | ~ v2_pre_topc(X1)
% 7.36/1.49      | ~ l1_pre_topc(X1)
% 7.36/1.49      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 7.36/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_437,plain,
% 7.36/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.36/1.49      | v2_struct_0(X1)
% 7.36/1.49      | ~ l1_pre_topc(X1)
% 7.36/1.49      | v1_funct_1(k4_tmap_1(X1,X0))
% 7.36/1.49      | sK1 != X1 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_438,plain,
% 7.36/1.49      ( ~ m1_pre_topc(X0,sK1)
% 7.36/1.49      | v2_struct_0(sK1)
% 7.36/1.49      | ~ l1_pre_topc(sK1)
% 7.36/1.49      | v1_funct_1(k4_tmap_1(sK1,X0)) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_437]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_442,plain,
% 7.36/1.49      ( ~ m1_pre_topc(X0,sK1) | v1_funct_1(k4_tmap_1(sK1,X0)) ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_438,c_33,c_31]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_517,plain,
% 7.36/1.49      ( v1_funct_1(k4_tmap_1(sK1,X0)) | sK1 != sK1 | sK2 != X0 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_29,c_442]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_518,plain,
% 7.36/1.49      ( v1_funct_1(k4_tmap_1(sK1,sK2)) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_517]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_20,plain,
% 7.36/1.49      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 7.36/1.49      | ~ m1_pre_topc(X1,X0)
% 7.36/1.49      | v2_struct_0(X0)
% 7.36/1.49      | ~ v2_pre_topc(X0)
% 7.36/1.49      | ~ l1_pre_topc(X0) ),
% 7.36/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_392,plain,
% 7.36/1.49      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 7.36/1.49      | ~ m1_pre_topc(X1,X0)
% 7.36/1.49      | v2_struct_0(X0)
% 7.36/1.49      | ~ l1_pre_topc(X0)
% 7.36/1.49      | sK1 != X0 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_393,plain,
% 7.36/1.49      ( v1_funct_2(k4_tmap_1(sK1,X0),u1_struct_0(X0),u1_struct_0(sK1))
% 7.36/1.49      | ~ m1_pre_topc(X0,sK1)
% 7.36/1.49      | v2_struct_0(sK1)
% 7.36/1.49      | ~ l1_pre_topc(sK1) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_392]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_397,plain,
% 7.36/1.49      ( v1_funct_2(k4_tmap_1(sK1,X0),u1_struct_0(X0),u1_struct_0(sK1))
% 7.36/1.49      | ~ m1_pre_topc(X0,sK1) ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_393,c_33,c_31]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_545,plain,
% 7.36/1.49      ( v1_funct_2(k4_tmap_1(sK1,X0),u1_struct_0(X0),u1_struct_0(sK1))
% 7.36/1.49      | sK1 != sK1
% 7.36/1.49      | sK2 != X0 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_29,c_397]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_546,plain,
% 7.36/1.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_545]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1148,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1591,plain,
% 7.36/1.49      ( k4_tmap_1(sK1,sK2) != X0 | sK3 != X0 | sK3 = k4_tmap_1(sK1,sK2) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_1148]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1592,plain,
% 7.36/1.49      ( k4_tmap_1(sK1,sK2) != k1_xboole_0
% 7.36/1.49      | sK3 = k4_tmap_1(sK1,sK2)
% 7.36/1.49      | sK3 != k1_xboole_0 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_1591]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1525,plain,
% 7.36/1.49      ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2119,plain,
% 7.36/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK3)
% 7.36/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_1968,c_1525]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2121,plain,
% 7.36/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK3)
% 7.36/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_1968,c_1528]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_756,plain,
% 7.36/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.36/1.49      | k4_tmap_1(sK1,sK2) != X0
% 7.36/1.49      | u1_struct_0(sK1) != k1_xboole_0
% 7.36/1.49      | u1_struct_0(sK2) != X1
% 7.36/1.49      | k1_xboole_0 = X0
% 7.36/1.49      | k1_xboole_0 = X1 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_546]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_757,plain,
% 7.36/1.49      ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.36/1.49      | u1_struct_0(sK1) != k1_xboole_0
% 7.36/1.49      | k1_xboole_0 = k4_tmap_1(sK1,sK2)
% 7.36/1.49      | k1_xboole_0 = u1_struct_0(sK2) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_756]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1521,plain,
% 7.36/1.49      ( u1_struct_0(sK1) != k1_xboole_0
% 7.36/1.49      | k1_xboole_0 = k4_tmap_1(sK1,sK2)
% 7.36/1.49      | k1_xboole_0 = u1_struct_0(sK2)
% 7.36/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2221,plain,
% 7.36/1.49      ( k4_tmap_1(sK1,sK2) = k1_xboole_0
% 7.36/1.49      | u1_struct_0(sK2) = k1_relat_1(sK3)
% 7.36/1.49      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_1968,c_1521]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_3249,plain,
% 7.36/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK3)
% 7.36/1.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_2177,c_372,c_511,c_518,c_546,c_1592,c_2119,c_2121,
% 7.36/1.49                 c_2221]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1879,plain,
% 7.36/1.49      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_relat_1(k4_tmap_1(sK1,sK2)) ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_1525,c_1534]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_813,plain,
% 7.36/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.36/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.36/1.49      | k4_tmap_1(sK1,sK2) != X0
% 7.36/1.49      | u1_struct_0(sK1) != X2
% 7.36/1.49      | u1_struct_0(sK2) != X1
% 7.36/1.49      | k1_xboole_0 = X2 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_546]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_814,plain,
% 7.36/1.49      ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.36/1.49      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = u1_struct_0(sK2)
% 7.36/1.49      | k1_xboole_0 = u1_struct_0(sK1) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_813]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_816,plain,
% 7.36/1.49      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = u1_struct_0(sK2)
% 7.36/1.49      | k1_xboole_0 = u1_struct_0(sK1) ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_814,c_511]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2181,plain,
% 7.36/1.49      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.49      | k1_relat_1(k4_tmap_1(sK1,sK2)) = u1_struct_0(sK2) ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_1879,c_816]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_16,plain,
% 7.36/1.49      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 7.36/1.49      | r1_tarski(X0,X1)
% 7.36/1.49      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.36/1.49      | ~ v1_funct_1(X1)
% 7.36/1.49      | ~ v1_funct_1(X0)
% 7.36/1.49      | ~ v1_relat_1(X0)
% 7.36/1.49      | ~ v1_relat_1(X1) ),
% 7.36/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1532,plain,
% 7.36/1.49      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.36/1.49      | r1_tarski(X0,X1) = iProver_top
% 7.36/1.49      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 7.36/1.49      | v1_funct_1(X1) != iProver_top
% 7.36/1.49      | v1_funct_1(X0) != iProver_top
% 7.36/1.49      | v1_relat_1(X0) != iProver_top
% 7.36/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_23,plain,
% 7.36/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.36/1.49      | ~ r2_hidden(X2,u1_struct_0(X0))
% 7.36/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.36/1.49      | v2_struct_0(X1)
% 7.36/1.49      | v2_struct_0(X0)
% 7.36/1.49      | ~ v2_pre_topc(X1)
% 7.36/1.49      | ~ l1_pre_topc(X1)
% 7.36/1.49      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 7.36/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_410,plain,
% 7.36/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.36/1.49      | ~ r2_hidden(X2,u1_struct_0(X0))
% 7.36/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.36/1.49      | v2_struct_0(X0)
% 7.36/1.49      | v2_struct_0(X1)
% 7.36/1.49      | ~ l1_pre_topc(X1)
% 7.36/1.49      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2
% 7.36/1.49      | sK1 != X1 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_411,plain,
% 7.36/1.49      ( ~ m1_pre_topc(X0,sK1)
% 7.36/1.49      | ~ r2_hidden(X1,u1_struct_0(X0))
% 7.36/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.36/1.49      | v2_struct_0(X0)
% 7.36/1.49      | v2_struct_0(sK1)
% 7.36/1.49      | ~ l1_pre_topc(sK1)
% 7.36/1.49      | k1_funct_1(k4_tmap_1(sK1,X0),X1) = X1 ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_410]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_415,plain,
% 7.36/1.49      ( ~ m1_pre_topc(X0,sK1)
% 7.36/1.49      | ~ r2_hidden(X1,u1_struct_0(X0))
% 7.36/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.36/1.49      | v2_struct_0(X0)
% 7.36/1.49      | k1_funct_1(k4_tmap_1(sK1,X0),X1) = X1 ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_411,c_33,c_31]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_524,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,u1_struct_0(X1))
% 7.36/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.36/1.49      | v2_struct_0(X1)
% 7.36/1.49      | k1_funct_1(k4_tmap_1(sK1,X1),X0) = X0
% 7.36/1.49      | sK1 != sK1
% 7.36/1.49      | sK2 != X1 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_29,c_415]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_525,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,u1_struct_0(sK2))
% 7.36/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.36/1.49      | v2_struct_0(sK2)
% 7.36/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_524]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_30,negated_conjecture,
% 7.36/1.50      ( ~ v2_struct_0(sK2) ),
% 7.36/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_529,plain,
% 7.36/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.36/1.50      | ~ r2_hidden(X0,u1_struct_0(sK2))
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_525,c_30]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_530,plain,
% 7.36/1.50      ( ~ r2_hidden(X0,u1_struct_0(sK2))
% 7.36/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_529]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1523,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
% 7.36/1.50      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 7.36/1.50      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_530]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3265,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_3249,c_1523]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_22,plain,
% 7.36/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.36/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.36/1.50      | ~ l1_pre_topc(X1) ),
% 7.36/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_488,plain,
% 7.36/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.36/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.36/1.50      | sK1 != X1 ),
% 7.36/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_489,plain,
% 7.36/1.50      ( ~ m1_pre_topc(X0,sK1)
% 7.36/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.36/1.50      inference(unflattening,[status(thm)],[c_488]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_503,plain,
% 7.36/1.50      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.36/1.50      | sK1 != sK1
% 7.36/1.50      | sK2 != X0 ),
% 7.36/1.50      inference(resolution_lifted,[status(thm)],[c_29,c_489]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_504,plain,
% 7.36/1.50      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.36/1.50      inference(unflattening,[status(thm)],[c_503]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1526,plain,
% 7.36/1.50      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3,plain,
% 7.36/1.50      ( ~ r2_hidden(X0,X1)
% 7.36/1.50      | m1_subset_1(X0,X2)
% 7.36/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 7.36/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1537,plain,
% 7.36/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.36/1.50      | m1_subset_1(X0,X2) = iProver_top
% 7.36/1.50      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2275,plain,
% 7.36/1.50      ( r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 7.36/1.50      | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1526,c_1537]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3259,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_3249,c_2275]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3734,plain,
% 7.36/1.50      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_3265,c_3259]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3735,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_3734]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3740,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1532,c_3735]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_28,negated_conjecture,
% 7.36/1.50      ( v1_funct_1(sK3) ),
% 7.36/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_39,plain,
% 7.36/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5,plain,
% 7.36/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.36/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1535,plain,
% 7.36/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4,plain,
% 7.36/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.36/1.50      | ~ v1_relat_1(X1)
% 7.36/1.50      | v1_relat_1(X0) ),
% 7.36/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1536,plain,
% 7.36/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.36/1.50      | v1_relat_1(X1) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2264,plain,
% 7.36/1.50      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1528,c_1536]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2517,plain,
% 7.36/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1535,c_2264]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4419,plain,
% 7.36/1.50      ( v1_relat_1(X0) != iProver_top
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_3740,c_39,c_2517]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4420,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_4419]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4427,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),u1_struct_0(sK2)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_2181,c_4420]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_519,plain,
% 7.36/1.50      ( v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_518]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2265,plain,
% 7.36/1.50      ( v1_relat_1(k4_tmap_1(sK1,sK2)) = iProver_top
% 7.36/1.50      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1525,c_1536]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2672,plain,
% 7.36/1.50      ( v1_relat_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1535,c_2265]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1,plain,
% 7.36/1.50      ( r1_tarski(X0,X0) ),
% 7.36/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1538,plain,
% 7.36/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2743,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_2181,c_1530]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4058,plain,
% 7.36/1.50      ( v1_relat_1(X0) != iProver_top
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_2743,c_519,c_2672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4059,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) != iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_4058]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4064,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1538,c_4059]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4627,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_4064,c_519,c_2672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4631,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_3249,c_4627]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2,plain,
% 7.36/1.50      ( r1_tarski(X0,X0) ),
% 7.36/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_108,plain,
% 7.36/1.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_0,plain,
% 7.36/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.36/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_112,plain,
% 7.36/1.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.36/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1584,plain,
% 7.36/1.50      ( u1_struct_0(sK2) != X0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | k1_xboole_0 != X0 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1148]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1648,plain,
% 7.36/1.50      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | k1_xboole_0 != u1_struct_0(sK2) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1584]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1147,plain,( X0 = X0 ),theory(equality) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1672,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1147]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1840,plain,
% 7.36/1.50      ( sK3 = sK3 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1147]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1704,plain,
% 7.36/1.50      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1148]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1941,plain,
% 7.36/1.50      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1704]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1942,plain,
% 7.36/1.50      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1941]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2031,plain,
% 7.36/1.50      ( X0 != X1 | X0 = u1_struct_0(sK1) | u1_struct_0(sK1) != X1 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1148]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2032,plain,
% 7.36/1.50      ( u1_struct_0(sK1) != k1_xboole_0
% 7.36/1.50      | k1_xboole_0 = u1_struct_0(sK1)
% 7.36/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_2031]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1150,plain,
% 7.36/1.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.36/1.50      theory(equality) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2133,plain,
% 7.36/1.50      ( ~ m1_subset_1(X0,X1)
% 7.36/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.36/1.50      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != X1
% 7.36/1.50      | sK3 != X0 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1150]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2688,plain,
% 7.36/1.50      ( ~ m1_subset_1(sK3,X0)
% 7.36/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.36/1.50      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != X0
% 7.36/1.50      | sK3 != sK3 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_2133]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3015,plain,
% 7.36/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.36/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.36/1.50      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
% 7.36/1.50      | sK3 != sK3 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_2688]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3239,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = k4_tmap_1(sK1,sK2) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1147]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2194,plain,
% 7.36/1.50      ( X0 != X1 | k4_tmap_1(sK1,sK2) != X1 | k4_tmap_1(sK1,sK2) = X0 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1148]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3338,plain,
% 7.36/1.50      ( X0 != k4_tmap_1(sK1,sK2)
% 7.36/1.50      | k4_tmap_1(sK1,sK2) = X0
% 7.36/1.50      | k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_2194]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3339,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2)
% 7.36/1.50      | k4_tmap_1(sK1,sK2) = k1_xboole_0
% 7.36/1.50      | k1_xboole_0 != k4_tmap_1(sK1,sK2) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_3338]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1151,plain,
% 7.36/1.50      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.36/1.50      theory(equality) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4026,plain,
% 7.36/1.50      ( k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0) != k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 7.36/1.50      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1151]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2143,plain,
% 7.36/1.50      ( ~ m1_subset_1(X0,X1)
% 7.36/1.50      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.36/1.50      | k4_tmap_1(sK1,sK2) != X0
% 7.36/1.50      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != X1 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1150]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2800,plain,
% 7.36/1.50      ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),X0)
% 7.36/1.50      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.36/1.50      | k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2)
% 7.36/1.50      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != X0 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_2143]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4762,plain,
% 7.36/1.50      ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.36/1.50      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)))
% 7.36/1.50      | k4_tmap_1(sK1,sK2) != k4_tmap_1(sK1,sK2)
% 7.36/1.50      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_2800]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1154,plain,
% 7.36/1.50      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 7.36/1.50      theory(equality) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5244,plain,
% 7.36/1.50      ( k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0) = k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 7.36/1.50      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 7.36/1.50      | k1_xboole_0 != u1_struct_0(sK1) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1154]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5270,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) = iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_4631,c_26,c_108,c_112,c_372,c_511,c_518,c_546,c_741,
% 7.36/1.50                 c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,c_3015,
% 7.36/1.50                 c_3239,c_3339,c_4026,c_4762,c_5244]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5278,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5270,c_4420]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7144,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_4427,c_26,c_108,c_112,c_372,c_511,c_518,c_519,c_546,
% 7.36/1.50                 c_741,c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,
% 7.36/1.50                 c_2672,c_3015,c_3239,c_3339,c_4026,c_4762,c_5244,c_5338]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7145,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_7144]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2744,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_2181,c_1530]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4316,plain,
% 7.36/1.50      ( v1_relat_1(X0) != iProver_top
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_2744,c_519,c_2672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4317,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(X0),u1_struct_0(sK2)) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_4316]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4322,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1538,c_4317]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4638,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),u1_struct_0(sK2)) = iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_4322,c_519,c_2672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4643,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_3249,c_4638]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5347,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) = iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_4643,c_26,c_108,c_112,c_372,c_511,c_518,c_546,c_741,
% 7.36/1.50                 c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,c_3015,
% 7.36/1.50                 c_3239,c_3339,c_4026,c_4762,c_5244]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2832,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK2)) = iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_2181,c_1532]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4555,plain,
% 7.36/1.50      ( v1_relat_1(X0) != iProver_top
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK2)) = iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_2832,c_519,c_2672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4556,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK2)) = iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_4555]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4564,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | m1_subset_1(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK1)) != iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_4556,c_1523]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4563,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | m1_subset_1(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK1)) = iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_4556,c_2275]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5256,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_4564,c_4563]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5257,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_5256]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5355,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5347,c_5257]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5999,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_5355,c_39,c_26,c_108,c_112,c_372,c_511,c_518,c_546,
% 7.36/1.50                 c_741,c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,
% 7.36/1.50                 c_2517,c_3015,c_3239,c_3339,c_4026,c_4762,c_5244]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1539,plain,
% 7.36/1.50      ( X0 = X1
% 7.36/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.36/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_6004,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5999,c_1539]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1703,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) != sK3
% 7.36/1.50      | sK3 = k4_tmap_1(sK1,sK2)
% 7.36/1.50      | sK3 != sK3 ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1591]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_6312,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_6004,c_372,c_511,c_518,c_546,c_1703,c_1840]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7151,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_7145,c_6312]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_15,plain,
% 7.36/1.50      ( r1_tarski(X0,X1)
% 7.36/1.50      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.36/1.50      | ~ v1_funct_1(X1)
% 7.36/1.50      | ~ v1_funct_1(X0)
% 7.36/1.50      | ~ v1_relat_1(X0)
% 7.36/1.50      | ~ v1_relat_1(X1)
% 7.36/1.50      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
% 7.36/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1533,plain,
% 7.36/1.50      ( k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 7.36/1.50      | r1_tarski(X1,X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X1) != iProver_top
% 7.36/1.50      | v1_relat_1(X1) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_9863,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_7151,c_1533]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7150,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_7145,c_1539]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_25,negated_conjecture,
% 7.36/1.50      ( ~ r2_hidden(X0,u1_struct_0(sK2))
% 7.36/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.36/1.50      | k1_funct_1(sK3,X0) = X0 ),
% 7.36/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1529,plain,
% 7.36/1.50      ( k1_funct_1(sK3,X0) = X0
% 7.36/1.50      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 7.36/1.50      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4565,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | m1_subset_1(sK0(k4_tmap_1(sK1,sK2),X0),u1_struct_0(sK1)) != iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_4556,c_1529]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5104,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_4565,c_4563]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5105,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_5104]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5356,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5347,c_5105]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5484,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_5356,c_39,c_26,c_108,c_112,c_372,c_511,c_518,c_546,
% 7.36/1.50                 c_741,c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,
% 7.36/1.50                 c_2517,c_3015,c_3239,c_3339,c_4026,c_4762,c_5244]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_17,plain,
% 7.36/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.36/1.50      | ~ r1_tarski(X1,X2)
% 7.36/1.50      | ~ v1_funct_1(X2)
% 7.36/1.50      | ~ v1_funct_1(X1)
% 7.36/1.50      | ~ v1_relat_1(X1)
% 7.36/1.50      | ~ v1_relat_1(X2)
% 7.36/1.50      | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
% 7.36/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1531,plain,
% 7.36/1.50      ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
% 7.36/1.50      | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
% 7.36/1.50      | r1_tarski(X2,X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X2) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X2) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2833,plain,
% 7.36/1.50      ( k1_funct_1(X0,sK0(X1,X2)) = k1_funct_1(X1,sK0(X1,X2))
% 7.36/1.50      | r1_tarski(X1,X0) != iProver_top
% 7.36/1.50      | r1_tarski(X1,X2) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(X1),k1_relat_1(X2)) != iProver_top
% 7.36/1.50      | v1_funct_1(X2) != iProver_top
% 7.36/1.50      | v1_funct_1(X1) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X1) != iProver_top
% 7.36/1.50      | v1_relat_1(X2) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1532,c_1531]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5570,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(X1,sK0(k4_tmap_1(sK1,sK2),X0))
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X1) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X1) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_2181,c_2833]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7514,plain,
% 7.36/1.50      ( v1_relat_1(X1) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(X1,sK0(k4_tmap_1(sK1,sK2),X0))
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X1) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_5570,c_519,c_2672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7515,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(X1,sK0(k4_tmap_1(sK1,sK2),X0))
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X1) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_7514]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7520,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5484,c_7515]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7532,plain,
% 7.36/1.50      ( v1_relat_1(X0) != iProver_top
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_7520,c_39,c_26,c_108,c_112,c_372,c_511,c_518,c_546,
% 7.36/1.50                 c_741,c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,
% 7.36/1.50                 c_2517,c_3015,c_3239,c_3339,c_4026,c_4762,c_5244]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7533,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_7532]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7540,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_3249,c_7533]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5489,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5484,c_1539]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3034,plain,
% 7.36/1.50      ( r1_tarski(X0,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(k4_tmap_1(sK1,sK2)))
% 7.36/1.50      | ~ v1_funct_1(X0)
% 7.36/1.50      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.36/1.50      | ~ v1_relat_1(X0)
% 7.36/1.50      | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0,k4_tmap_1(sK1,sK2))) != k1_funct_1(X0,sK0(X0,k4_tmap_1(sK1,sK2))) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_6876,plain,
% 7.36/1.50      ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2)))
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.36/1.50      | ~ v1_funct_1(sK3)
% 7.36/1.50      | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
% 7.36/1.50      | ~ v1_relat_1(sK3)
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_3034]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_6877,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2)))
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_6876]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2742,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(X1,X0)
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
% 7.36/1.50      | v1_funct_1(X1) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(X1) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_2181,c_1531]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3858,plain,
% 7.36/1.50      ( v1_relat_1(X1) != iProver_top
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(X1,X0)
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
% 7.36/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_2742,c_519,c_2672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3859,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(X1,X0)
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X1) != iProver_top
% 7.36/1.50      | v1_funct_1(X1) != iProver_top
% 7.36/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_3858]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5492,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5484,c_3859]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_6667,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_5492,c_39,c_26,c_108,c_112,c_372,c_511,c_518,c_546,
% 7.36/1.50                 c_741,c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,
% 7.36/1.50                 c_2517,c_3015,c_3239,c_3339,c_4026,c_4762,c_5244]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_6668,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_6667]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_6674,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = k1_funct_1(sK3,X0)
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_3249,c_6668]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_6682,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1532,c_6674]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7864,plain,
% 7.36/1.50      ( v1_relat_1(X0) != iProver_top
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_6682,c_39,c_2517]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7865,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = k1_funct_1(sK3,sK0(sK3,X0))
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_7864]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_7872,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2)))
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5270,c_7865]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_8150,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_7540,c_39,c_372,c_511,c_518,c_519,c_546,c_1703,c_1840,
% 7.36/1.50                 c_2517,c_2672,c_5270,c_5489,c_6877,c_7872]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_10022,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_9863,c_39,c_372,c_511,c_518,c_519,c_546,c_1703,c_1840,
% 7.36/1.50                 c_2517,c_2672,c_5347,c_7150,c_8150]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_10024,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) != sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_10022,c_1533]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3270,plain,
% 7.36/1.50      ( k1_funct_1(sK3,X0) = X0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_3249,c_1529]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3441,plain,
% 7.36/1.50      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | k1_funct_1(sK3,X0) = X0 ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_3270,c_3259]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3442,plain,
% 7.36/1.50      ( k1_funct_1(sK3,X0) = X0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_3441]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3447,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1532,c_3442]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3847,plain,
% 7.36/1.50      ( v1_relat_1(X0) != iProver_top
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_3447,c_39,c_2517]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3848,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_3847]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5279,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5270,c_3848]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5870,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_5279,c_519,c_2672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5875,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5870,c_1539]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_6305,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_5875,c_372,c_511,c_518,c_546,c_1703,c_1840]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_6309,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5999,c_6305]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_8461,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_6309,c_1533]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2519,plain,
% 7.36/1.50      ( v1_relat_1(sK3) ),
% 7.36/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_2517]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2674,plain,
% 7.36/1.50      ( v1_relat_1(k4_tmap_1(sK1,sK2)) ),
% 7.36/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_2672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5349,plain,
% 7.36/1.50      ( r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.36/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_5347]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5878,plain,
% 7.36/1.50      ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.36/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_5875]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_8462,plain,
% 7.36/1.50      ( r1_tarski(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3))
% 7.36/1.50      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.36/1.50      | ~ v1_funct_1(sK3)
% 7.36/1.50      | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
% 7.36/1.50      | ~ v1_relat_1(sK3)
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.36/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_8461]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_8730,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_8461,c_28,c_372,c_511,c_518,c_546,c_1703,c_1840,
% 7.36/1.50                 c_2519,c_2674,c_5349,c_5878,c_8150,c_8462]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_10027,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_10024,c_39,c_519,c_2517,c_2672,c_5270,c_8730]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_4561,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_relat_1(sK3)) = iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_3249,c_4556]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5276,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3)
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5270,c_1539]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5353,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3)
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5347,c_1539]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5583,plain,
% 7.36/1.50      ( k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_5276,c_5270,c_5353]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5584,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_relat_1(sK3) ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_5583]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5594,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_relat_1(sK3)) = iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5584,c_1532]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_6118,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_relat_1(sK3)) = iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_4561,c_519,c_2672,c_5594]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_6124,plain,
% 7.36/1.50      ( k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),X1)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X1))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X1) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X1)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X1) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(X1) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_6118,c_1531]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_9238,plain,
% 7.36/1.50      ( v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X1) != iProver_top
% 7.36/1.50      | k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),X1)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X1))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X1) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X1)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_6124,c_39,c_2517]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_9239,plain,
% 7.36/1.50      ( k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),X1)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X1))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X1) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X1)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X1) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_9238]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_9248,plain,
% 7.36/1.50      ( k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),X1)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X1))
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X1) = iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X1)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X1) != iProver_top
% 7.36/1.50      | v1_relat_1(X1) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_2181,c_9239]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_9606,plain,
% 7.36/1.50      ( k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),X1)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X1))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X1) = iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X1)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X1) != iProver_top
% 7.36/1.50      | v1_relat_1(X1) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_9248,c_26,c_108,c_112,c_372,c_511,c_518,c_546,c_741,
% 7.36/1.50                 c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,c_3015,
% 7.36/1.50                 c_3239,c_3339,c_4026,c_4762,c_5244]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_9607,plain,
% 7.36/1.50      ( k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),X1)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X1))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X1) = iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X1)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X1) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_9606]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_10037,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_10027,c_9607]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_13728,plain,
% 7.36/1.50      ( v1_relat_1(X0) != iProver_top
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_10037,c_519,c_2672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_13729,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_13728]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_13739,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_3249,c_13729]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_13749,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1530,c_13739]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_10035,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_10027,c_1539]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_10046,plain,
% 7.36/1.50      ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.36/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_10035]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5351,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3)) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_2181,c_5347]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_5499,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3)) = iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_5351,c_26,c_108,c_112,c_372,c_511,c_518,c_546,c_741,
% 7.36/1.50                 c_757,c_1592,c_1648,c_1672,c_1840,c_1942,c_2032,c_3015,
% 7.36/1.50                 c_3239,c_3339,c_4026,c_4762,c_5244]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_13738,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5499,c_13729]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_9246,plain,
% 7.36/1.50      ( k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_5347,c_9239]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_12556,plain,
% 7.36/1.50      ( v1_relat_1(X0) != iProver_top
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3))
% 7.36/1.50      | r1_tarski(sK3,X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_9246,c_39,c_372,c_511,c_518,c_546,c_1703,c_1840,
% 7.36/1.50                 c_2517,c_10035]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_12557,plain,
% 7.36/1.50      ( k1_funct_1(X0,sK0(k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(sK3,X0) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_12556]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_12563,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_10027,c_12557]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_13949,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_13738,c_519,c_2672,c_12563]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_13950,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3))
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_13949]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_13951,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = k1_xboole_0
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_13950,c_1533]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_13952,plain,
% 7.36/1.50      ( r1_tarski(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | ~ r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3))
% 7.36/1.50      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.36/1.50      | ~ v1_funct_1(sK3)
% 7.36/1.50      | ~ v1_relat_1(k4_tmap_1(sK1,sK2))
% 7.36/1.50      | ~ v1_relat_1(sK3)
% 7.36/1.50      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.36/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_13951]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_13954,plain,
% 7.36/1.50      ( u1_struct_0(sK2) = k1_xboole_0 ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_13749,c_28,c_372,c_511,c_518,c_546,c_1703,c_1840,
% 7.36/1.50                 c_2519,c_2674,c_5349,c_10046,c_13952]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14039,plain,
% 7.36/1.50      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_relat_1(k4_tmap_1(sK1,sK2)) ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_13954,c_1879]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14046,plain,
% 7.36/1.50      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK1) = k1_xboole_0 ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_13954,c_816]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_11,plain,
% 7.36/1.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.36/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.36/1.50      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.36/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_789,plain,
% 7.36/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.36/1.50      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 7.36/1.50      | k4_tmap_1(sK1,sK2) != X0
% 7.36/1.50      | u1_struct_0(sK1) != X1
% 7.36/1.50      | u1_struct_0(sK2) != k1_xboole_0 ),
% 7.36/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_546]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_790,plain,
% 7.36/1.50      ( ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 7.36/1.50      | k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK2) != k1_xboole_0 ),
% 7.36/1.50      inference(unflattening,[status(thm)],[c_789]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_791,plain,
% 7.36/1.50      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK2) != k1_xboole_0
% 7.36/1.50      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14047,plain,
% 7.36/1.50      ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) = iProver_top ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_13954,c_1525]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14769,plain,
% 7.36/1.50      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),k4_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_14046,c_28,c_372,c_511,c_518,c_546,c_791,c_1703,
% 7.36/1.50                 c_1840,c_2519,c_2674,c_5349,c_10046,c_13952,c_14047]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_15328,plain,
% 7.36/1.50      ( k1_relat_1(k4_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_14039,c_14769]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_15343,plain,
% 7.36/1.50      ( r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_15328,c_1532]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_15355,plain,
% 7.36/1.50      ( r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_15343,c_15328]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16508,plain,
% 7.36/1.50      ( v1_relat_1(X0) != iProver_top
% 7.36/1.50      | r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_15355,c_519,c_2672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16509,plain,
% 7.36/1.50      ( r2_hidden(sK0(k4_tmap_1(sK1,sK2),X0),k1_xboole_0) = iProver_top
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_16508]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14044,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
% 7.36/1.50      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.36/1.50      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_13954,c_1523]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14034,plain,
% 7.36/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.36/1.50      | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_13954,c_2275]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14623,plain,
% 7.36/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0 ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_14044,c_14034]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14624,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),X0) = X0
% 7.36/1.50      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_14623]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16514,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_16509,c_14624]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14042,plain,
% 7.36/1.50      ( u1_struct_0(sK1) = k1_xboole_0 | k1_relat_1(sK3) = k1_xboole_0 ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_13954,c_1968]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14050,plain,
% 7.36/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) = iProver_top ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_13954,c_1528]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_776,plain,
% 7.36/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.36/1.50      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK1) != X1
% 7.36/1.50      | u1_struct_0(sK2) != k1_xboole_0
% 7.36/1.50      | sK3 != X0 ),
% 7.36/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_777,plain,
% 7.36/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 7.36/1.50      | k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK2) != k1_xboole_0 ),
% 7.36/1.50      inference(unflattening,[status(thm)],[c_776]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1520,plain,
% 7.36/1.50      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
% 7.36/1.50      | u1_struct_0(sK2) != k1_xboole_0
% 7.36/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14043,plain,
% 7.36/1.50      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
% 7.36/1.50      | k1_xboole_0 != k1_xboole_0
% 7.36/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_13954,c_1520]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14051,plain,
% 7.36/1.50      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_xboole_0
% 7.36/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.36/1.50      inference(equality_resolution_simp,[status(thm)],[c_14043]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14045,plain,
% 7.36/1.50      ( k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_13954,c_1878]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14052,plain,
% 7.36/1.50      ( k1_relat_1(sK3) = k1_xboole_0
% 7.36/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_14051,c_14045]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14701,plain,
% 7.36/1.50      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_14042,c_14050,c_14052]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14714,plain,
% 7.36/1.50      ( r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_14701,c_1532]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14726,plain,
% 7.36/1.50      ( r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_14714,c_14701]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16085,plain,
% 7.36/1.50      ( v1_relat_1(X0) != iProver_top
% 7.36/1.50      | r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_14726,c_39,c_2517]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16086,plain,
% 7.36/1.50      ( r2_hidden(sK0(sK3,X0),k1_xboole_0) = iProver_top
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_16085]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16091,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,X0)) = sK0(sK3,X0)
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_16086,c_14624]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16227,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_15328,c_16091]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_107,plain,
% 7.36/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_109,plain,
% 7.36/1.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_107]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19400,plain,
% 7.36/1.50      ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_16227,c_109,c_519,c_2672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19401,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_19400]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16669,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = X0
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.36/1.50      | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_16514,c_1539]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19416,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_19401,c_16669]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19421,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_19416,c_14701]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19657,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_19421,c_39,c_109,c_372,c_511,c_518,c_546,c_1703,
% 7.36/1.50                 c_1840,c_2517]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19658,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_19657]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19659,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_19658,c_1533]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19660,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(light_normalisation,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_19659,c_14701,c_15328]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19408,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_19401,c_1539]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14049,plain,
% 7.36/1.50      ( k1_funct_1(sK3,X0) = X0
% 7.36/1.50      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.36/1.50      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 7.36/1.50      inference(demodulation,[status(thm)],[c_13954,c_1529]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14203,plain,
% 7.36/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.36/1.50      | k1_funct_1(sK3,X0) = X0 ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_14049,c_14034]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_14204,plain,
% 7.36/1.50      ( k1_funct_1(sK3,X0) = X0
% 7.36/1.50      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_14203]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16515,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_16509,c_14204]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16640,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = X0
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),X0)) = sK0(k4_tmap_1(sK1,sK2),X0)
% 7.36/1.50      | r1_tarski(X0,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_16515,c_1539]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19417,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_19401,c_16640]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19420,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_19417,c_14701]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19435,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_19420,c_39,c_109,c_372,c_511,c_518,c_546,c_1703,
% 7.36/1.50                 c_1840,c_2517]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19436,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_19435]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19663,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_19660,c_39,c_109,c_372,c_511,c_518,c_519,c_546,c_1703,
% 7.36/1.50                 c_1840,c_2517,c_2672,c_19408,c_19436]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19665,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) != sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(k1_relat_1(sK3),k1_relat_1(k4_tmap_1(sK1,sK2))) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_19663,c_1533]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16092,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(sK3,X0)) = sK0(sK3,X0)
% 7.36/1.50      | r1_tarski(sK3,X0) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.36/1.50      | v1_funct_1(X0) != iProver_top
% 7.36/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_16086,c_14204]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16101,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_15328,c_16092]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16231,plain,
% 7.36/1.50      ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_16101,c_109,c_519,c_2672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16232,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_16231]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16237,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_16232,c_1539]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16362,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_16237,c_372,c_511,c_518,c_546,c_1703,c_1840]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16670,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_16514,c_16362]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16679,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_16670,c_14701]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_17068,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_16679,c_39,c_109,c_2517]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_17069,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.36/1.50      inference(renaming,[status(thm)],[c_17068]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_17070,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_17069,c_1533]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_17071,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(light_normalisation,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_17070,c_14701,c_15328]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16641,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_16515,c_16362]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_16650,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_16641,c_14701]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_17742,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(sK3,k4_tmap_1(sK1,sK2))) = sK0(sK3,k4_tmap_1(sK1,sK2)) ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_17071,c_39,c_109,c_372,c_511,c_518,c_519,c_546,c_1703,
% 7.36/1.50                 c_1840,c_2517,c_2672,c_16237,c_16650]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19666,plain,
% 7.36/1.50      ( sK0(sK3,k4_tmap_1(sK1,sK2)) != sK0(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(light_normalisation,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_19665,c_14701,c_15328,c_17742]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19667,plain,
% 7.36/1.50      ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(equality_resolution_simp,[status(thm)],[c_19666]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19793,plain,
% 7.36/1.50      ( r1_tarski(sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_19667,c_39,c_109,c_519,c_2517,c_2672]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19801,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_19793,c_1539]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1588,plain,
% 7.36/1.50      ( ~ r1_tarski(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | ~ r1_tarski(sK3,k4_tmap_1(sK1,sK2))
% 7.36/1.50      | sK3 = k4_tmap_1(sK1,sK2) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1589,plain,
% 7.36/1.50      ( sK3 = k4_tmap_1(sK1,sK2)
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top
% 7.36/1.50      | r1_tarski(sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_1588]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19834,plain,
% 7.36/1.50      ( r1_tarski(k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_19801,c_39,c_109,c_372,c_511,c_518,c_519,c_546,c_1589,
% 7.36/1.50                 c_2517,c_2672,c_19667]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19838,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_16514,c_19834]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19841,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_19838,c_14701]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19809,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_19793,c_16669]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19814,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_19809,c_14701]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_20076,plain,
% 7.36/1.50      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_19841,c_39,c_109,c_372,c_511,c_518,c_546,c_1703,
% 7.36/1.50                 c_1840,c_2517,c_19814]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_20078,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.36/1.50      | r1_tarski(k1_relat_1(k4_tmap_1(sK1,sK2)),k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_20076,c_1533]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19839,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_16515,c_19834]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19840,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_19839,c_14701]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19810,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_19793,c_16640]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19813,plain,
% 7.36/1.50      ( k4_tmap_1(sK1,sK2) = sK3
% 7.36/1.50      | k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(light_normalisation,[status(thm)],[c_19810,c_14701]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19966,plain,
% 7.36/1.50      ( k1_funct_1(sK3,sK0(k4_tmap_1(sK1,sK2),sK3)) = sK0(k4_tmap_1(sK1,sK2),sK3) ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_19840,c_39,c_109,c_372,c_511,c_518,c_546,c_1703,
% 7.36/1.50                 c_1840,c_2517,c_19813]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_20079,plain,
% 7.36/1.50      ( sK0(k4_tmap_1(sK1,sK2),sK3) != sK0(k4_tmap_1(sK1,sK2),sK3)
% 7.36/1.50      | r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(light_normalisation,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_20078,c_14701,c_15328,c_19966]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_20080,plain,
% 7.36/1.50      ( r1_tarski(k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.36/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.36/1.50      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_funct_1(sK3) != iProver_top
% 7.36/1.50      | v1_relat_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.36/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.36/1.50      inference(equality_resolution_simp,[status(thm)],[c_20079]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(contradiction,plain,
% 7.36/1.50      ( $false ),
% 7.36/1.50      inference(minisat,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_20080,c_19667,c_2672,c_2517,c_1589,c_546,c_519,c_518,
% 7.36/1.50                 c_511,c_372,c_109,c_39]) ).
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.36/1.50  
% 7.36/1.50  ------                               Statistics
% 7.36/1.50  
% 7.36/1.50  ------ General
% 7.36/1.50  
% 7.36/1.50  abstr_ref_over_cycles:                  0
% 7.36/1.50  abstr_ref_under_cycles:                 0
% 7.36/1.50  gc_basic_clause_elim:                   0
% 7.36/1.50  forced_gc_time:                         0
% 7.36/1.50  parsing_time:                           0.009
% 7.36/1.50  unif_index_cands_time:                  0.
% 7.36/1.50  unif_index_add_time:                    0.
% 7.36/1.50  orderings_time:                         0.
% 7.36/1.50  out_proof_time:                         0.036
% 7.36/1.50  total_time:                             0.579
% 7.36/1.50  num_of_symbols:                         54
% 7.36/1.50  num_of_terms:                           7407
% 7.36/1.50  
% 7.36/1.50  ------ Preprocessing
% 7.36/1.50  
% 7.36/1.50  num_of_splits:                          0
% 7.36/1.50  num_of_split_atoms:                     0
% 7.36/1.50  num_of_reused_defs:                     0
% 7.36/1.50  num_eq_ax_congr_red:                    11
% 7.36/1.50  num_of_sem_filtered_clauses:            1
% 7.36/1.50  num_of_subtypes:                        0
% 7.36/1.50  monotx_restored_types:                  0
% 7.36/1.50  sat_num_of_epr_types:                   0
% 7.36/1.50  sat_num_of_non_cyclic_types:            0
% 7.36/1.50  sat_guarded_non_collapsed_types:        0
% 7.36/1.50  num_pure_diseq_elim:                    0
% 7.36/1.50  simp_replaced_by:                       0
% 7.36/1.50  res_preprocessed:                       132
% 7.36/1.50  prep_upred:                             0
% 7.36/1.50  prep_unflattend:                        61
% 7.36/1.50  smt_new_axioms:                         0
% 7.36/1.50  pred_elim_cands:                        5
% 7.36/1.50  pred_elim:                              6
% 7.36/1.50  pred_elim_cl:                           9
% 7.36/1.50  pred_elim_cycles:                       9
% 7.36/1.50  merged_defs:                            0
% 7.36/1.50  merged_defs_ncl:                        0
% 7.36/1.50  bin_hyper_res:                          0
% 7.36/1.50  prep_cycles:                            4
% 7.36/1.50  pred_elim_time:                         0.009
% 7.36/1.50  splitting_time:                         0.
% 7.36/1.50  sem_filter_time:                        0.
% 7.36/1.50  monotx_time:                            0.
% 7.36/1.50  subtype_inf_time:                       0.
% 7.36/1.50  
% 7.36/1.50  ------ Problem properties
% 7.36/1.50  
% 7.36/1.50  clauses:                                24
% 7.36/1.50  conjectures:                            3
% 7.36/1.50  epr:                                    3
% 7.36/1.50  horn:                                   19
% 7.36/1.50  ground:                                 12
% 7.36/1.50  unary:                                  8
% 7.36/1.50  binary:                                 3
% 7.36/1.50  lits:                                   70
% 7.36/1.50  lits_eq:                                21
% 7.36/1.50  fd_pure:                                0
% 7.36/1.50  fd_pseudo:                              0
% 7.36/1.50  fd_cond:                                0
% 7.36/1.50  fd_pseudo_cond:                         1
% 7.36/1.50  ac_symbols:                             0
% 7.36/1.50  
% 7.36/1.50  ------ Propositional Solver
% 7.36/1.50  
% 7.36/1.50  prop_solver_calls:                      35
% 7.36/1.50  prop_fast_solver_calls:                 3896
% 7.36/1.50  smt_solver_calls:                       0
% 7.36/1.50  smt_fast_solver_calls:                  0
% 7.36/1.50  prop_num_of_clauses:                    6378
% 7.36/1.50  prop_preprocess_simplified:             11524
% 7.36/1.50  prop_fo_subsumed:                       549
% 7.36/1.50  prop_solver_time:                       0.
% 7.36/1.50  smt_solver_time:                        0.
% 7.36/1.50  smt_fast_solver_time:                   0.
% 7.36/1.50  prop_fast_solver_time:                  0.
% 7.36/1.50  prop_unsat_core_time:                   0.
% 7.36/1.50  
% 7.36/1.50  ------ QBF
% 7.36/1.50  
% 7.36/1.50  qbf_q_res:                              0
% 7.36/1.50  qbf_num_tautologies:                    0
% 7.36/1.50  qbf_prep_cycles:                        0
% 7.36/1.50  
% 7.36/1.50  ------ BMC1
% 7.36/1.50  
% 7.36/1.50  bmc1_current_bound:                     -1
% 7.36/1.50  bmc1_last_solved_bound:                 -1
% 7.36/1.50  bmc1_unsat_core_size:                   -1
% 7.36/1.50  bmc1_unsat_core_parents_size:           -1
% 7.36/1.50  bmc1_merge_next_fun:                    0
% 7.36/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.36/1.50  
% 7.36/1.50  ------ Instantiation
% 7.36/1.50  
% 7.36/1.50  inst_num_of_clauses:                    1773
% 7.36/1.50  inst_num_in_passive:                    525
% 7.36/1.50  inst_num_in_active:                     1071
% 7.36/1.50  inst_num_in_unprocessed:                177
% 7.36/1.50  inst_num_of_loops:                      1390
% 7.36/1.50  inst_num_of_learning_restarts:          0
% 7.36/1.50  inst_num_moves_active_passive:          312
% 7.36/1.50  inst_lit_activity:                      0
% 7.36/1.50  inst_lit_activity_moves:                0
% 7.36/1.50  inst_num_tautologies:                   0
% 7.36/1.50  inst_num_prop_implied:                  0
% 7.36/1.50  inst_num_existing_simplified:           0
% 7.36/1.50  inst_num_eq_res_simplified:             0
% 7.36/1.50  inst_num_child_elim:                    0
% 7.36/1.50  inst_num_of_dismatching_blockings:      764
% 7.36/1.50  inst_num_of_non_proper_insts:           3743
% 7.36/1.50  inst_num_of_duplicates:                 0
% 7.36/1.50  inst_inst_num_from_inst_to_res:         0
% 7.36/1.50  inst_dismatching_checking_time:         0.
% 7.36/1.50  
% 7.36/1.50  ------ Resolution
% 7.36/1.50  
% 7.36/1.50  res_num_of_clauses:                     0
% 7.36/1.50  res_num_in_passive:                     0
% 7.36/1.50  res_num_in_active:                      0
% 7.36/1.50  res_num_of_loops:                       136
% 7.36/1.50  res_forward_subset_subsumed:            476
% 7.36/1.50  res_backward_subset_subsumed:           2
% 7.36/1.50  res_forward_subsumed:                   0
% 7.36/1.50  res_backward_subsumed:                  0
% 7.36/1.50  res_forward_subsumption_resolution:     0
% 7.36/1.50  res_backward_subsumption_resolution:    3
% 7.36/1.50  res_clause_to_clause_subsumption:       2793
% 7.36/1.50  res_orphan_elimination:                 0
% 7.36/1.50  res_tautology_del:                      424
% 7.36/1.50  res_num_eq_res_simplified:              0
% 7.36/1.50  res_num_sel_changes:                    0
% 7.36/1.50  res_moves_from_active_to_pass:          0
% 7.36/1.50  
% 7.36/1.50  ------ Superposition
% 7.36/1.50  
% 7.36/1.50  sup_time_total:                         0.
% 7.36/1.50  sup_time_generating:                    0.
% 7.36/1.50  sup_time_sim_full:                      0.
% 7.36/1.50  sup_time_sim_immed:                     0.
% 7.36/1.50  
% 7.36/1.50  sup_num_of_clauses:                     203
% 7.36/1.50  sup_num_in_active:                      86
% 7.36/1.50  sup_num_in_passive:                     117
% 7.36/1.50  sup_num_of_loops:                       276
% 7.36/1.50  sup_fw_superposition:                   565
% 7.36/1.50  sup_bw_superposition:                   397
% 7.36/1.50  sup_immediate_simplified:               365
% 7.36/1.50  sup_given_eliminated:                   2
% 7.36/1.50  comparisons_done:                       0
% 7.36/1.50  comparisons_avoided:                    485
% 7.36/1.50  
% 7.36/1.50  ------ Simplifications
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  sim_fw_subset_subsumed:                 123
% 7.36/1.50  sim_bw_subset_subsumed:                 116
% 7.36/1.50  sim_fw_subsumed:                        128
% 7.36/1.50  sim_bw_subsumed:                        33
% 7.36/1.50  sim_fw_subsumption_res:                 0
% 7.36/1.50  sim_bw_subsumption_res:                 0
% 7.36/1.50  sim_tautology_del:                      19
% 7.36/1.50  sim_eq_tautology_del:                   209
% 7.36/1.50  sim_eq_res_simp:                        6
% 7.36/1.50  sim_fw_demodulated:                     3
% 7.36/1.50  sim_bw_demodulated:                     103
% 7.36/1.50  sim_light_normalised:                   126
% 7.36/1.50  sim_joinable_taut:                      0
% 7.36/1.50  sim_joinable_simp:                      0
% 7.36/1.50  sim_ac_normalised:                      0
% 7.36/1.50  sim_smt_subsumption:                    0
% 7.36/1.50  
%------------------------------------------------------------------------------
